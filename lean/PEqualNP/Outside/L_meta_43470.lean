import PEqualNP.Defs

-- The ordered live-circuit search follows the checked L_meta_41466 (Apache-2.0).
-- The input pairs and the eleven-gate circuit here are specific to L_meta_43470.
namespace PEqualNP.Outside.L_meta_43470_aux

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)
end Live

abbrev W := BitVec 256
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 256 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 256)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 256) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (BitVec.ofNat 256 0)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 100000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩


section Fast

def nP : ℕ := 128
def fullM : ℕ := 2 ^ nP - 1
def hiM : ℕ := Nat.shiftLeft (2 ^ nP - 1) nP
def allM : ℕ := 2 ^ (nP + nP) - 1
def sp (x : ℕ) : ℕ := Nat.xor (Nat.shiftRight x nP) x
def cutN (l : List ℕ) : ℕ := List.rec 0 (fun w _ ih => Nat.lor (Nat.xor (Nat.shiftRight w nP) w) ih) l
def memN (z : ℕ) (l : List ℕ) : Bool := List.rec false (fun w _ ih => Bool.rec ih true (Nat.beq z w)) l
def app (l r : List ℕ) : List ℕ := List.rec r (fun w _ ih => w :: ih) l
def isGoal (ws : List ℕ) : Bool :=
  List.rec false (fun w t _ => List.rec (Bool.rec (Nat.beq w fullM) true (Nat.beq w hiM)) (fun _ _ _ => false) t) ws
def anyK (f : ℕ → List ℕ → Bool) (l : List (ℕ × List ℕ)) : Bool :=
  List.rec false (fun c _ ih => Bool.rec ih true (f c.1 c.2)) l
def hdK (l : List (ℕ × List ℕ)) : ℕ × List ℕ := List.rec (0, []) (fun c _ _ => c) l
def dz (base z : ℕ) : ℕ := Nat.sub allM (Nat.lor (Nat.xor (Nat.shiftRight z nP) z) base)
def keep2 (e1 a b : ℕ) (r : List ℕ) (z : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Nat.rec tail (fun e2 _ => (e2, z :: a :: b :: r) :: tail) e1
def keepB (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Bool.rec (keep2 e1 a b r z tail) ((e1, z :: b :: r) :: keep2 e1 a b r z tail)
    (Nat.beq (dz (Nat.lor base (sp b)) z) 0)
def keepA (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Bool.rec (keepB e1 a b r base z tail) ((e1, z :: a :: r) :: keepB e1 a b r base z tail)
    (Nat.beq (dz (Nat.lor base (sp a)) z) 0)
def keeps (e a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Nat.rec tail (fun e1 _ => keepA e1 a b r base z tail) e
def cand0 (e a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Bool.rec (keeps e a b r base z tail) ((e, z :: r) :: keeps e a b r base z tail) (Nat.beq (dz base z) 0)
def cand (e thr a b : ℕ) (ws r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Bool.rec tail (Bool.rec (cand0 e a b r base z tail) tail (memN z ws)) (Nat.ble thr z)
def opsN (a b : ℕ) : List ℕ := [Nat.land a b, Nat.lor a b, Nat.xor a (Nat.land a b), Nat.xor b (Nat.land a b)]
def pairKS (e thr a b : ℕ) (ws r : List ℕ) (base : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  cand e thr a b ws r base (Nat.land a b) (cand e thr a b ws r base (Nat.lor a b)
    (cand e thr a b ws r base (Nat.xor a (Nat.land a b)) (cand e thr a b ws r base (Nat.xor b (Nat.land a b)) tail)))
def forceN (z : ℕ) (k : ℕ → List (ℕ × List ℕ)) : List (ℕ × List ℕ) := Nat.rec (k Nat.zero) (fun m _ => k (Nat.succ m)) z
def revK (pre acc : List ℕ) (k : List ℕ → List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  List.rec (fun acc => k acc) (fun p _ ih acc => ih (p :: acc)) pre acc
def insK (x : ℕ) (l : List ℕ) (k : List ℕ → List (ℕ × List ℕ)) : List ℕ → List (ℕ × List ℕ) :=
  List.rec (fun pre => revK pre [x] k)
    (fun y ys ih pre => Bool.rec (ih (y :: pre)) (revK pre (x :: y :: ys) k) (Nat.ble x y)) l
def mkR (thr : ℕ) (sk rest : List ℕ) (k : List ℕ → List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Nat.rec (revK sk rest k) (fun _ _ => revK sk rest (fun L => List.rec (k []) (fun h t _ => insK h t k []) L)) thr
def sortK (l : List ℕ) : (List ℕ → List (ℕ × List ℕ)) → List (ℕ × List ℕ) :=
  List.rec (fun k => k []) (fun x _ ih k => ih (fun s => forceN x (fun x' => insK x' s k []))) l
def canonMap (l : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  List.rec [] (fun c _ ih => Nat.rec
    (List.rec ih (fun z t _ => sortK t (fun s => forceN z (fun z' => (Nat.zero, z' :: s) :: ih))) c.2)
    (fun _ _ => c :: ih) c.1) l
def prodN (z : ℕ) (l : List ℕ) : ℕ := List.rec 1 (fun w _ ih => Nat.mul ih (Nat.xor z w)) l
def candZ (thr : ℕ) (ws r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Bool.rec tail (Bool.rec (forceN z (fun z' => (Nat.zero, z' :: r) :: tail)) tail (Nat.beq (prodN z ws) 0))
    (Nat.beq (Nat.add (dz base z) (Nat.sub thr z)) 0)
def pairZ (thr a b : ℕ) (ws r : List ℕ) (base : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  candZ thr ws r base (Nat.land a b) (candZ thr ws r base (Nat.lor a b)
    (candZ thr ws r base (Nat.xor a (Nat.land a b)) (candZ thr ws r base (Nat.xor b (Nat.land a b)) tail)))
def pairK (e thr a b : ℕ) (ws r : List ℕ) (base : ℕ) (tail : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  Nat.rec (pairZ thr a b ws r base tail) (fun _ _ => pairKS e thr a b ws r base tail) e
def flt0 (a b base : ℕ) : Bool :=
  Nat.beq (Nat.mul
    (Nat.mul (Nat.sub allM (Nat.lor (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b)) base))
      (Nat.sub allM (Nat.lor (Nat.xor (Nat.xor (Nat.xor (Nat.shiftRight a nP) a) (Nat.xor (Nat.shiftRight b nP) b))
        (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b))) base)))
    (Nat.mul
      (Nat.sub allM (Nat.lor (Nat.xor (Nat.xor (Nat.shiftRight a nP) a)
        (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b))) base))
      (Nat.sub allM (Nat.lor (Nat.xor (Nat.xor (Nat.shiftRight b nP) b)
        (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b))) base)))) 0
def fltT (_ _ _ : ℕ) : Bool := true
def innerK (flt : ℕ → ℕ → ℕ → Bool) (e thr : ℕ) (ws : List ℕ) (a : ℕ) (post : List ℕ) :
    ℕ → List ℕ → List (ℕ × List ℕ) → List (ℕ × List ℕ) :=
  List.rec (fun _ _ tail => tail)
    (fun b rest ih acc sk tail =>
      Bool.rec (ih (Nat.lor acc (Nat.xor (Nat.shiftRight b nP) b)) (b :: sk) tail)
        (mkR thr sk rest (fun r => pairK e thr a b ws r (Nat.lor acc (cutN rest))
          (ih (Nat.lor acc (Nat.xor (Nat.shiftRight b nP) b)) (b :: sk) tail)))
        (flt a b (Nat.lor acc (cutN rest))))
    post
def outerK (flt : ℕ → ℕ → ℕ → Bool) (e thr : ℕ) (ws : List ℕ) (post : List ℕ) :
    ℕ → List ℕ → List (ℕ × List ℕ) → List (ℕ × List ℕ) :=
  List.rec (fun _ _ tail => tail)
    (fun a post ih acc pre tail =>
      innerK flt e thr ws a post acc pre (ih (Nat.lor acc (Nat.xor (Nat.shiftRight a nP) a)) (a :: pre) tail))
    post
def kidsG (flt : ℕ → ℕ → ℕ → Bool) (e h : ℕ) (t ws : List ℕ) : List (ℕ × List ℕ) :=
  innerK flt e 0 ws h t hiM []
    (outerK flt e h ws t (Nat.lor hiM (Nat.xor (Nat.shiftRight h nP) h)) [h] [])
def kids (e : ℕ) (ws : List ℕ) : List (ℕ × List ℕ) :=
  List.rec [] (fun h t _ => Nat.rec (kidsG flt0 e h t ws) (fun _ _ => canonMap (kidsG fltT e h t ws)) e) ws
def kidsRoot (e : ℕ) (ws : List ℕ) : List (ℕ × List ℕ) :=
  canonMap (Nat.rec (outerK flt0 e 0 ws ws hiM [] []) (fun _ _ => outerK fltT e 0 ws ws hiM [] []) e)
def crossC (l : List ℕ) : ℕ → ℕ → Bool :=
  List.rec (fun p q => Bool.rec (Bool.rec true false (Nat.beq q 0)) false (Nat.beq p 0))
    (fun w _ ih p q =>
      Bool.rec (Bool.rec (Bool.rec (ih (Nat.xor p (Nat.land p w)) (Nat.xor q (Nat.land q (Nat.shiftRight w nP))))
        true (ih (Nat.land p w) (Nat.land q (Nat.shiftRight w nP)))) false (Nat.beq q 0)) false (Nat.beq p 0))
    l
def collOK (c : ℕ) (ws : List ℕ) : Bool := Nat.rec true (fun _ _ => Bool.rec true false (crossC ws fullM fullM)) c
def node (c k : ℕ) : ℕ → List ℕ → Bool :=
  Nat.rec (fun _ ws => isGoal ws)
    (fun _ ih e ws => Bool.rec (Bool.rec false (anyK ih (kids e ws)) (collOK c ws)) true (isGoal ws)) k
def root (c k e : ℕ) (ws : List ℕ) : Bool := Bool.rec (anyK (node c k) (kidsRoot e ws)) true (isGoal ws)
def cutFull (ws : List ℕ) : Bool := Nat.beq (Nat.sub allM (Nat.lor (cutN ws) hiM)) 0
def searchN (c k : ℕ) (inputs : List ℕ) : Bool :=
  inputs.sublists.any fun ws => decide (ws.length ≤ k + 2) && cutFull ws && root c k (k + 2 - ws.length) ws

set_option maxRecDepth 100000 in
theorem brec_eq {α : Type} (x y : α) (c : Bool) : (Bool.rec x y c : α) = if c = true then y else x := by
  cases c <;> rfl

set_option maxRecDepth 100000 in
theorem sp_bit (x i : ℕ) : (sp x).testBit i = Bool.xor (x.testBit (nP + i)) (x.testBit i) := by
  rw [show sp x = (x >>> nP) ^^^ x from rfl, Nat.testBit_xor, Nat.testBit_shiftRight]

set_option maxRecDepth 100000 in
theorem cutN_bit (l : List ℕ) (i : ℕ) : (cutN l).testBit i = true ↔ ∃ w ∈ l, (sp w).testBit i = true := by
  induction l with
  | nil => simp [show cutN [] = 0 from rfl]
  | cons w l ih =>
    rw [show cutN (w :: l) = sp w ||| cutN l from rfl, Nat.testBit_or, Bool.or_eq_true, ih]
    simp

set_option maxRecDepth 100000 in
theorem ge_of_bits (m x : ℕ) (h : ∀ i < m, x.testBit i = true) : 2 ^ m - 1 ≤ x := by
  have e : x % 2 ^ m = 2 ^ m - 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
    by_cases hi : i < m
    · simp [hi, h i hi]
    · simp [hi]
  rw [← e]
  exact Nat.mod_le _ _

set_option maxRecDepth 100000 in
theorem hiM_bit (i : ℕ) (h1 : nP ≤ i) (h2 : i < nP + nP) : hiM.testBit i = true := by
  rw [show hiM = (2 ^ nP - 1) <<< nP from rfl, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega

set_option maxRecDepth 100000 in
theorem pass_of (base z : ℕ) (hlo : ∀ i < nP, (sp z).testBit i = true ∨ base.testBit i = true)
    (hhi : ∀ i, nP ≤ i → i < nP + nP → base.testBit i = true) : Nat.beq (dz base z) 0 = true := by
  have le : allM ≤ sp z ||| base := by
    apply ge_of_bits
    intro i hi
    rw [Nat.testBit_or, Bool.or_eq_true]
    by_cases c : i < nP
    · exact hlo i c
    · exact Or.inr (hhi i (by omega) hi)
  have z0 : dz base z = 0 := Nat.sub_eq_zero_of_le le
  rw [z0]
  rfl

def accOK (acc : ℕ) (sk : List ℕ) : Prop :=
  (∀ i, nP ≤ i → i < nP + nP → acc.testBit i = true) ∧
  (∀ w ∈ sk, ∀ i, (sp w).testBit i = true → acc.testBit i = true)

set_option maxRecDepth 100000 in
theorem accOK_nil : accOK hiM [] := ⟨hiM_bit, by simp⟩

set_option maxRecDepth 100000 in
theorem accOK_cons {acc : ℕ} {sk : List ℕ} (h : accOK acc sk) (b : ℕ) :
    accOK (Nat.lor acc (Nat.xor (Nat.shiftRight b nP) b)) (b :: sk) := by
  change accOK (acc ||| sp b) (b :: sk)
  refine ⟨fun i h1 h2 => ?_, fun w hw i hi => ?_⟩
  · rw [Nat.testBit_or, h.1 i h1 h2]; rfl
  · rw [Nat.testBit_or, Bool.or_eq_true]
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inr hi
    · exact Or.inl (h.2 w hw i hi)

set_option maxRecDepth 100000 in
theorem app_eq (l r : List ℕ) : app l r = l ++ r := by
  induction l with
  | nil => rfl
  | cons w l ih => change w :: app l r = w :: (l ++ r); rw [ih]

set_option maxRecDepth 100000 in
theorem forceN_eq (z : ℕ) (k : ℕ → List (ℕ × List ℕ)) : forceN z k = k z := by
  cases z <;> rfl

set_option maxRecDepth 100000 in
theorem revK_eq (k : List ℕ → List (ℕ × List ℕ)) : ∀ (pre acc : List ℕ), revK pre acc k = k (pre.reverse ++ acc) := by
  intro pre
  induction pre with
  | nil => intro acc; rfl
  | cons p pre ih =>
    intro acc
    change revK pre (p :: acc) k = k ((p :: pre).reverse ++ acc)
    rw [ih, List.reverse_cons, List.append_assoc]
    rfl

set_option maxRecDepth 100000 in
theorem insK_eq (x : ℕ) : ∀ l : List ℕ, ∃ r : List ℕ, r.Perm (x :: l) ∧
    ∀ (k : List ℕ → List (ℕ × List ℕ)) (pre : List ℕ), insK x l k pre = k (pre.reverse ++ r) := by
  intro l
  induction l with
  | nil => exact ⟨[x], List.Perm.refl _, fun k pre => revK_eq k pre [x]⟩
  | cons y ys ih =>
    obtain ⟨r, hr, hk⟩ := ih
    cases hb : Nat.ble x y
    · refine ⟨y :: r, (hr.cons y).trans (List.Perm.swap x y ys), fun k pre => ?_⟩
      change (Bool.rec (insK x ys k (y :: pre)) (revK pre (x :: y :: ys) k) (Nat.ble x y) : List (ℕ × List ℕ)) = _
      rw [hb]
      change insK x ys k (y :: pre) = _
      rw [hk, List.reverse_cons, List.append_assoc]
      rfl
    · refine ⟨x :: y :: ys, List.Perm.refl _, fun k pre => ?_⟩
      change (Bool.rec (insK x ys k (y :: pre)) (revK pre (x :: y :: ys) k) (Nat.ble x y) : List (ℕ × List ℕ)) = _
      rw [hb]
      exact revK_eq k pre _

set_option maxRecDepth 100000 in
theorem mkR_eq (thr : ℕ) (sk rest : List ℕ) : ∃ r : List ℕ, r.Perm (sk ++ rest) ∧
    ∀ k : List ℕ → List (ℕ × List ℕ), mkR thr sk rest k = k r := by
  have p0 : (sk.reverse ++ rest).Perm (sk ++ rest) := (List.reverse_perm sk).append_right rest
  cases thr with
  | zero => exact ⟨sk.reverse ++ rest, p0, fun k => revK_eq k sk rest⟩
  | succ t =>
    cases hL : sk.reverse ++ rest with
    | nil =>
      rw [hL] at p0
      refine ⟨[], p0, fun k => ?_⟩
      change revK sk rest (fun L => List.rec (k []) (fun h t _ => insK h t k []) L) = k []
      rw [revK_eq, hL]
    | cons h tl =>
      rw [hL] at p0
      obtain ⟨r, hr, hk⟩ := insK_eq h tl
      refine ⟨r, hr.trans p0, fun k => ?_⟩
      change revK sk rest (fun L => List.rec (k []) (fun h t _ => insK h t k []) L) = k r
      rw [revK_eq, hL]
      exact hk k []

set_option maxRecDepth 100000 in
theorem sortK_eq : ∀ l : List ℕ, ∃ s : List ℕ, s.Perm l ∧
    ∀ k : List ℕ → List (ℕ × List ℕ), sortK l k = k s := by
  intro l
  induction l with
  | nil => exact ⟨[], List.Perm.refl _, fun k => rfl⟩
  | cons x xs ih =>
    obtain ⟨s, hs, hk⟩ := ih
    obtain ⟨r, hr, hi⟩ := insK_eq x s
    refine ⟨r, hr.trans (hs.cons x), fun k => ?_⟩
    change sortK xs (fun s => forceN x (fun x' => insK x' s k [])) = k r
    rw [hk, forceN_eq]
    exact hi k []

set_option maxRecDepth 100000 in
theorem canonMap_hit : ∀ (l : List (ℕ × List ℕ)) (e' z : ℕ) (kept : List ℕ), (e', z :: kept) ∈ l →
    ∃ kept' : List ℕ, kept'.Perm kept ∧ (e', z :: kept') ∈ canonMap l := by
  intro l
  induction l with
  | nil => intro e' z kept h; simp at h
  | cons c l ih =>
    intro e' z kept h
    have unf : canonMap (c :: l) = (Nat.rec
        (List.rec (canonMap l) (fun z t _ => sortK t (fun s => forceN z (fun z' => (Nat.zero, z' :: s) :: canonMap l))) c.2)
        (fun _ _ => c :: canonMap l) c.1 : List (ℕ × List ℕ)) := rfl
    have mono : ∀ c', c' ∈ canonMap l → c' ∈ canonMap (c :: l) := by
      intro c' hc'
      rw [unf]
      obtain ⟨e0, ws0⟩ := c
      cases e0 with
      | zero =>
        cases ws0 with
        | nil => exact hc'
        | cons z0 t0 =>
          obtain ⟨s, _, hk⟩ := sortK_eq t0
          change c' ∈ sortK t0 (fun s => forceN z0 (fun z' => (Nat.zero, z' :: s) :: canonMap l))
          rw [hk, forceN_eq]
          exact List.mem_cons_of_mem _ hc'
      | succ e1 => exact List.mem_cons_of_mem _ hc'
    rcases List.mem_cons.mp h with hc | h
    · subst hc
      cases e' with
      | zero =>
        obtain ⟨s, hs, hk⟩ := sortK_eq kept
        refine ⟨s, hs, ?_⟩
        rw [unf]
        change (0, z :: s) ∈ sortK kept (fun s => forceN z (fun z' => (Nat.zero, z' :: s) :: canonMap l))
        rw [hk, forceN_eq]
        exact List.mem_cons_self
      | succ e1 =>
        refine ⟨kept, List.Perm.refl _, ?_⟩
        rw [unf]
        exact List.mem_cons_self
    · obtain ⟨kept', hp, hm⟩ := ih e' z kept h
      exact ⟨kept', hp, mono _ hm⟩

set_option maxRecDepth 100000 in
theorem memN_false (z : ℕ) (l : List ℕ) (h : z ∉ l) : memN z l = false := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    change (Bool.rec (memN z l) true (Nat.beq z w) : Bool) = false
    cases hb : Nat.beq z w
    · exact ih (fun hm => h (List.mem_cons_of_mem _ hm))
    · exact absurd (Nat.eq_of_beq_eq_true hb) (fun e => h (e ▸ List.mem_cons_self))

set_option maxRecDepth 100000 in
theorem keep2_mono {c : ℕ × List ℕ} (e1 a b : ℕ) (r : List ℕ) (z : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ keep2 e1 a b r z tail := by
  cases e1 with
  | zero => exact h
  | succ e2 => exact List.mem_cons_of_mem _ h

set_option maxRecDepth 100000 in
theorem keepB_mono {c : ℕ × List ℕ} (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ keepB e1 a b r base z tail := by
  unfold keepB
  rw [brec_eq]
  split
  · exact List.mem_cons_of_mem _ (keep2_mono e1 a b r z h)
  · exact keep2_mono e1 a b r z h

set_option maxRecDepth 100000 in
theorem keepA_mono {c : ℕ × List ℕ} (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ keepA e1 a b r base z tail := by
  unfold keepA
  rw [brec_eq]
  split
  · exact List.mem_cons_of_mem _ (keepB_mono e1 a b r base z h)
  · exact keepB_mono e1 a b r base z h

set_option maxRecDepth 100000 in
theorem keeps_mono {c : ℕ × List ℕ} (e a b : ℕ) (r : List ℕ) (base z : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ keeps e a b r base z tail := by
  cases e with
  | zero => exact h
  | succ e1 => exact keepA_mono e1 a b r base z h

set_option maxRecDepth 100000 in
theorem cand0_mono {c : ℕ × List ℕ} (e a b : ℕ) (r : List ℕ) (base z : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ cand0 e a b r base z tail := by
  unfold cand0
  rw [brec_eq]
  split
  · exact List.mem_cons_of_mem _ (keeps_mono e a b r base z h)
  · exact keeps_mono e a b r base z h

set_option maxRecDepth 100000 in
theorem cand_mono {c : ℕ × List ℕ} (e thr a b : ℕ) (ws r : List ℕ) (base z : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ cand e thr a b ws r base z tail := by
  unfold cand
  rw [brec_eq, brec_eq]
  split
  · split
    · exact h
    · exact cand0_mono e a b r base z h
  · exact h

set_option maxRecDepth 100000 in
theorem cand_eq (e thr a b : ℕ) (ws r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (hthr : thr ≤ z) (hfresh : z ∉ ws) :
    cand e thr a b ws r base z tail = cand0 e a b r base z tail := by
  unfold cand
  rw [Nat.ble_eq_true_of_le hthr, memN_false z ws hfresh]

set_option maxRecDepth 100000 in
theorem cand0_none (e a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (hp : Nat.beq (dz base z) 0 = true) : (e, z :: r) ∈ cand0 e a b r base z tail := by
  unfold cand0
  rw [hp]
  exact List.mem_cons_self

set_option maxRecDepth 100000 in
theorem cand0_of_keeps {c : ℕ × List ℕ} (e a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (h : c ∈ keeps e a b r base z tail) : c ∈ cand0 e a b r base z tail := by
  unfold cand0
  rw [brec_eq]
  split
  · exact List.mem_cons_of_mem _ h
  · exact h

set_option maxRecDepth 100000 in
theorem keepA_of_keepB {c : ℕ × List ℕ} (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (h : c ∈ keepB e1 a b r base z tail) : c ∈ keepA e1 a b r base z tail := by
  unfold keepA
  rw [brec_eq]
  split
  · exact List.mem_cons_of_mem _ h
  · exact h

set_option maxRecDepth 100000 in
theorem keepB_of_keep2 {c : ℕ × List ℕ} (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (h : c ∈ keep2 e1 a b r z tail) : c ∈ keepB e1 a b r base z tail := by
  unfold keepB
  rw [brec_eq]
  split
  · exact List.mem_cons_of_mem _ h
  · exact h

set_option maxRecDepth 100000 in
theorem cand0_a (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (hp : Nat.beq (dz (Nat.lor base (sp a)) z) 0 = true) :
    (e1, z :: a :: r) ∈ cand0 (e1 + 1) a b r base z tail := by
  apply cand0_of_keeps
  change (e1, z :: a :: r) ∈ keepA e1 a b r base z tail
  unfold keepA
  rw [hp]
  exact List.mem_cons_self

set_option maxRecDepth 100000 in
theorem cand0_b (e1 a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (hp : Nat.beq (dz (Nat.lor base (sp b)) z) 0 = true) :
    (e1, z :: b :: r) ∈ cand0 (e1 + 1) a b r base z tail := by
  apply cand0_of_keeps
  change (e1, z :: b :: r) ∈ keepA e1 a b r base z tail
  apply keepA_of_keepB
  unfold keepB
  rw [hp]
  exact List.mem_cons_self

set_option maxRecDepth 100000 in
theorem cand0_ab (e2 a b : ℕ) (r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) :
    (e2, z :: a :: b :: r) ∈ cand0 (e2 + 2) a b r base z tail := by
  apply cand0_of_keeps
  change (e2, z :: a :: b :: r) ∈ keepA (e2 + 1) a b r base z tail
  apply keepA_of_keepB
  apply keepB_of_keep2
  exact List.mem_cons_self

set_option maxRecDepth 100000 in
theorem pairKS_hit {c : ℕ × List ℕ} (e thr a b : ℕ) (ws r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ))
    (hz : z ∈ opsN a b) (h : ∀ tail', c ∈ cand e thr a b ws r base z tail') :
    c ∈ pairKS e thr a b ws r base tail := by
  simp only [opsN, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold pairKS
  rcases hz with rfl | rfl | rfl | rfl
  · exact h _
  · exact cand_mono _ _ _ _ _ _ _ _ (h _)
  · exact cand_mono _ _ _ _ _ _ _ _ (cand_mono _ _ _ _ _ _ _ _ (h _))
  · exact cand_mono _ _ _ _ _ _ _ _ (cand_mono _ _ _ _ _ _ _ _ (cand_mono _ _ _ _ _ _ _ _ (h _)))

set_option maxRecDepth 100000 in
theorem pairKS_mono {c : ℕ × List ℕ} (e thr a b : ℕ) (ws r : List ℕ) (base : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ pairKS e thr a b ws r base tail :=
  cand_mono _ _ _ _ _ _ _ _ (cand_mono _ _ _ _ _ _ _ _ (cand_mono _ _ _ _ _ _ _ _ (cand_mono _ _ _ _ _ _ _ _ h)))

set_option maxRecDepth 100000 in
theorem xor_zero_eq (z w : ℕ) (h : Nat.xor z w = 0) : z = w := by
  apply Nat.eq_of_testBit_eq
  intro i
  have e := congrArg (fun y => Nat.testBit y i) h
  change (z ^^^ w).testBit i = (0 : ℕ).testBit i at e
  rw [Nat.testBit_xor, Nat.zero_testBit] at e
  revert e
  cases z.testBit i <;> cases w.testBit i <;> decide

set_option maxRecDepth 100000 in
theorem prodN_ne (z : ℕ) (l : List ℕ) (h : z ∉ l) : prodN z l ≠ 0 := by
  induction l with
  | nil => exact Nat.one_ne_zero
  | cons w l ih =>
    change Nat.mul (prodN z l) (Nat.xor z w) ≠ 0
    exact Nat.mul_ne_zero (ih (fun hm => h (List.mem_cons_of_mem _ hm)))
      (fun e0 => h (xor_zero_eq z w e0 ▸ List.mem_cons_self))

set_option maxRecDepth 100000 in
theorem candZ_mono {c : ℕ × List ℕ} (thr : ℕ) (ws r : List ℕ) (base z : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ candZ thr ws r base z tail := by
  unfold candZ
  cases Nat.beq (Nat.add (dz base z) (Nat.sub thr z)) 0
  · exact h
  · cases Nat.beq (prodN z ws) 0
    · rw [forceN_eq]
      exact List.mem_cons_of_mem _ h
    · exact h

set_option maxRecDepth 100000 in
theorem candZ_hit (thr : ℕ) (ws r : List ℕ) (base z : ℕ) (tail : List (ℕ × List ℕ)) (hthr : thr ≤ z)
    (hfresh : z ∉ ws) (hp : Nat.beq (dz base z) 0 = true) : (0, z :: r) ∈ candZ thr ws r base z tail := by
  have e0 : Nat.add (dz base z) (Nat.sub thr z) = 0 := by
    rw [Nat.eq_of_beq_eq_true hp]
    change 0 + (thr - z) = 0
    rw [Nat.sub_eq_zero_of_le hthr]
  have e1 : Nat.beq (prodN z ws) 0 = false := by
    cases hb : Nat.beq (prodN z ws) 0
    · rfl
    · exact absurd (Nat.eq_of_beq_eq_true hb) (prodN_ne z ws hfresh)
  unfold candZ
  rw [e0, e1, forceN_eq]
  exact List.mem_cons_self

set_option maxRecDepth 100000 in
theorem pairZ_mono {c : ℕ × List ℕ} (thr a b : ℕ) (ws r : List ℕ) (base : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ pairZ thr a b ws r base tail :=
  candZ_mono _ _ _ _ _ (candZ_mono _ _ _ _ _ (candZ_mono _ _ _ _ _ (candZ_mono _ _ _ _ _ h)))

set_option maxRecDepth 100000 in
theorem pairZ_hit (thr a b z : ℕ) (ws r : List ℕ) (base : ℕ) (tail : List (ℕ × List ℕ)) (hz : z ∈ opsN a b)
    (hthr : thr ≤ z) (hfresh : z ∉ ws) (hp : Nat.beq (dz base z) 0 = true) :
    (0, z :: r) ∈ pairZ thr a b ws r base tail := by
  simp only [opsN, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold pairZ
  rcases hz with rfl | rfl | rfl | rfl
  · exact candZ_hit _ _ _ _ _ _ hthr hfresh hp
  · exact candZ_mono _ _ _ _ _ (candZ_hit _ _ _ _ _ _ hthr hfresh hp)
  · exact candZ_mono _ _ _ _ _ (candZ_mono _ _ _ _ _ (candZ_hit _ _ _ _ _ _ hthr hfresh hp))
  · exact candZ_mono _ _ _ _ _ (candZ_mono _ _ _ _ _ (candZ_mono _ _ _ _ _ (candZ_hit _ _ _ _ _ _ hthr hfresh hp)))

set_option maxRecDepth 100000 in
theorem pairK_mono {c : ℕ × List ℕ} (e thr a b : ℕ) (ws r : List ℕ) (base : ℕ) {tail : List (ℕ × List ℕ)}
    (h : c ∈ tail) : c ∈ pairK e thr a b ws r base tail := by
  cases e with
  | zero => exact pairZ_mono thr a b ws r base h
  | succ e1 => exact pairKS_mono (e1 + 1) thr a b ws r base h

set_option maxRecDepth 100000 in
theorem opsN_swap {a b z : ℕ} (h : z ∈ opsN a b) : z ∈ opsN b a := by
  simp only [opsN, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  have c1 : Nat.land b a = Nat.land a b := Nat.land_comm b a
  have c2 : Nat.lor b a = Nat.lor a b := Nat.lor_comm b a
  rw [c1, c2]
  tauto

set_option maxRecDepth 100000 in
theorem sp_xor (a b : ℕ) : sp (Nat.xor a b) = Nat.xor (sp a) (sp b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (sp (a ^^^ b)).testBit i = (sp a ^^^ sp b).testBit i
  rw [sp_bit, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_xor, sp_bit, sp_bit]
  cases a.testBit (nP + i) <;> cases a.testBit i <;> cases b.testBit (nP + i) <;> cases b.testBit i <;> rfl

set_option maxRecDepth 100000 in
theorem lor_eq (a b : ℕ) : Nat.lor a b = Nat.xor (Nat.xor a b) (Nat.land a b) := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (a ||| b).testBit i = ((a ^^^ b) ^^^ (a &&& b)).testBit i
  rw [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit i <;> cases b.testBit i <;> rfl

set_option maxRecDepth 100000 in
theorem flt0_ok (a b base z : ℕ) (hz : z ∈ opsN a b) (hp : Nat.beq (dz base z) 0 = true) :
    flt0 a b base = true := by
  have hd : dz base z = 0 := Nat.eq_of_beq_eq_true hp
  have e1 : dz base (Nat.land a b) =
      Nat.sub allM (Nat.lor (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b)) base) := rfl
  have e2 : dz base (Nat.lor a b) =
      Nat.sub allM (Nat.lor (Nat.xor (Nat.xor (Nat.xor (Nat.shiftRight a nP) a) (Nat.xor (Nat.shiftRight b nP) b))
        (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b))) base) := by
    change Nat.sub allM (Nat.lor (sp (Nat.lor a b)) base) = Nat.sub allM (Nat.lor (Nat.xor (Nat.xor (sp a) (sp b)) (sp (Nat.land a b))) base)
    rw [show Nat.lor a b = Nat.xor (Nat.xor a b) (Nat.land a b) from lor_eq a b, sp_xor, sp_xor]
  have e3 : dz base (Nat.xor a (Nat.land a b)) =
      Nat.sub allM (Nat.lor (Nat.xor (Nat.xor (Nat.shiftRight a nP) a)
        (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b))) base) := by
    change Nat.sub allM (Nat.lor (sp (Nat.xor a (Nat.land a b))) base) = Nat.sub allM (Nat.lor (Nat.xor (sp a) (sp (Nat.land a b))) base)
    rw [sp_xor]
  have e4 : dz base (Nat.xor b (Nat.land a b)) =
      Nat.sub allM (Nat.lor (Nat.xor (Nat.xor (Nat.shiftRight b nP) b)
        (Nat.xor (Nat.shiftRight (Nat.land a b) nP) (Nat.land a b))) base) := by
    change Nat.sub allM (Nat.lor (sp (Nat.xor b (Nat.land a b))) base) = Nat.sub allM (Nat.lor (Nat.xor (sp b) (sp (Nat.land a b))) base)
    rw [sp_xor]
  unfold flt0
  rw [← e1, ← e2, ← e3, ← e4]
  simp only [opsN, List.mem_cons, List.not_mem_nil, or_false] at hz
  have prod : Nat.mul (Nat.mul (dz base (Nat.land a b)) (dz base (Nat.lor a b)))
      (Nat.mul (dz base (Nat.xor a (Nat.land a b))) (dz base (Nat.xor b (Nat.land a b)))) = 0 := by
    change dz base (Nat.land a b) * dz base (Nat.lor a b) *
      (dz base (Nat.xor a (Nat.land a b)) * dz base (Nat.xor b (Nat.land a b))) = 0
    rcases hz with rfl | rfl | rfl | rfl
    · rw [hd, Nat.zero_mul, Nat.zero_mul]
    · rw [hd, Nat.mul_zero, Nat.zero_mul]
    · rw [hd, Nat.zero_mul, Nat.mul_zero]
    · rw [hd, Nat.mul_zero, Nat.mul_zero]
  rw [prod]
  rfl

def fltOK (flt : ℕ → ℕ → ℕ → Bool) (e : ℕ) : Prop :=
  ∀ a b base z, z ∈ opsN a b → (Nat.beq (dz base z) 0 = true ∨ 0 < e) → flt a b base = true

set_option maxRecDepth 100000 in
theorem innerK_mono {c : ℕ × List ℕ} (flt : ℕ → ℕ → ℕ → Bool) (e thr : ℕ) (ws : List ℕ) (a : ℕ) :
    ∀ (post : List ℕ) (acc : ℕ) (sk : List ℕ) (tail : List (ℕ × List ℕ)), c ∈ tail →
      c ∈ innerK flt e thr ws a post acc sk tail := by
  intro post
  induction post with
  | nil => intro acc sk tail h; exact h
  | cons b rest ih =>
    intro acc sk tail h
    change c ∈ (Bool.rec (innerK flt e thr ws a rest (Nat.lor acc (Nat.xor (Nat.shiftRight b nP) b)) (b :: sk) tail)
      (mkR thr sk rest (fun r => pairK e thr a b ws r (Nat.lor acc (cutN rest))
        (innerK flt e thr ws a rest (Nat.lor acc (Nat.xor (Nat.shiftRight b nP) b)) (b :: sk) tail)))
      (flt a b (Nat.lor acc (cutN rest))) : List (ℕ × List ℕ))
    rw [brec_eq]
    split
    · obtain ⟨r, _, hk⟩ := mkR_eq thr sk rest
      rw [hk]
      exact pairK_mono _ _ _ _ _ _ _ (ih _ _ _ h)
    · exact ih _ _ _ h

set_option maxRecDepth 100000 in
theorem inner_hit (flt : ℕ → ℕ → ℕ → Bool) (e thr : ℕ) (ws : List ℕ) (a b : ℕ) (Q : ℕ × List ℕ → Prop) :
    ∀ (post : List ℕ) (acc : ℕ) (sk : List ℕ) (tail : List (ℕ × List ℕ)), b ∈ post → accOK acc sk →
      (∀ sk' rest' acc', (b :: (sk' ++ rest')).Perm (sk ++ post) → accOK acc' sk' →
        flt a b (Nat.lor acc' (cutN rest')) = true ∧
        ∀ r : List ℕ, r.Perm (sk' ++ rest') →
          ∃ c, Q c ∧ ∀ tail', c ∈ pairK e thr a b ws r (Nat.lor acc' (cutN rest')) tail') →
      ∃ c, Q c ∧ c ∈ innerK flt e thr ws a post acc sk tail := by
  intro post
  induction post with
  | nil => intro acc sk tail hb; simp at hb
  | cons b0 rest ih =>
    intro acc sk tail hb hacc cb
    have unf : innerK flt e thr ws a (b0 :: rest) acc sk tail =
        (Bool.rec (innerK flt e thr ws a rest (Nat.lor acc (Nat.xor (Nat.shiftRight b0 nP) b0)) (b0 :: sk) tail)
          (mkR thr sk rest (fun r => pairK e thr a b0 ws r (Nat.lor acc (cutN rest))
            (innerK flt e thr ws a rest (Nat.lor acc (Nat.xor (Nat.shiftRight b0 nP) b0)) (b0 :: sk) tail)))
          (flt a b0 (Nat.lor acc (cutN rest))) : List (ℕ × List ℕ)) := rfl
    by_cases hbb : b = b0
    · subst hbb
      obtain ⟨hf, hall⟩ := cb sk rest acc List.perm_middle.symm hacc
      obtain ⟨r, hr, hk⟩ := mkR_eq thr sk rest
      obtain ⟨c, hq, hc⟩ := hall r hr
      refine ⟨c, hq, ?_⟩
      rw [unf, hf, hk]
      exact hc _
    · have hb' : b ∈ rest := (List.mem_cons.mp hb).resolve_left hbb
      obtain ⟨c, hq, hc⟩ := ih (Nat.lor acc (Nat.xor (Nat.shiftRight b0 nP) b0)) (b0 :: sk) tail hb'
        (accOK_cons hacc b0) (fun sk' rest' acc' hp ha => cb sk' rest' acc'
          (hp.trans (by simpa using (List.perm_middle (a := b0) (l₁ := sk) (l₂ := rest)).symm)) ha)
      refine ⟨c, hq, ?_⟩
      rw [unf, brec_eq]
      split
      · obtain ⟨r, _, hk⟩ := mkR_eq thr sk rest
        rw [hk]
        exact pairK_mono _ _ _ _ _ _ _ hc
      · exact hc

set_option maxRecDepth 100000 in
theorem outerK_mono {c : ℕ × List ℕ} (flt : ℕ → ℕ → ℕ → Bool) (e thr : ℕ) (ws : List ℕ) :
    ∀ (post : List ℕ) (acc : ℕ) (pre : List ℕ) (tail : List (ℕ × List ℕ)), c ∈ tail →
      c ∈ outerK flt e thr ws post acc pre tail := by
  intro post
  induction post with
  | nil => intro acc pre tail h; exact h
  | cons a post ih =>
    intro acc pre tail h
    exact innerK_mono flt e thr ws a post acc pre _ (ih _ _ _ h)

set_option maxRecDepth 100000 in
theorem outer_hit (flt : ℕ → ℕ → ℕ → Bool) (e thr : ℕ) (ws : List ℕ) (a b : ℕ) (Q : ℕ × List ℕ → Prop) :
    ∀ (post : List ℕ) (acc : ℕ) (pre : List ℕ) (tail : List (ℕ × List ℕ)), a ∈ post → b ∈ post → a ≠ b →
      accOK acc pre →
      (∀ x y sk' rest' acc', ((x = a ∧ y = b) ∨ (x = b ∧ y = a)) → (x :: y :: (sk' ++ rest')).Perm (pre ++ post) →
        accOK acc' sk' →
        flt x y (Nat.lor acc' (cutN rest')) = true ∧
        ∀ r : List ℕ, r.Perm (sk' ++ rest') →
          ∃ c, Q c ∧ ∀ tail', c ∈ pairK e thr x y ws r (Nat.lor acc' (cutN rest')) tail') →
      ∃ c, Q c ∧ c ∈ outerK flt e thr ws post acc pre tail := by
  intro post
  induction post with
  | nil => intro acc pre tail ha; simp at ha
  | cons x0 post ih =>
    intro acc pre tail ha hb hab hacc cb
    have unf : outerK flt e thr ws (x0 :: post) acc pre tail =
        innerK flt e thr ws x0 post acc pre
          (outerK flt e thr ws post (Nat.lor acc (Nat.xor (Nat.shiftRight x0 nP) x0)) (x0 :: pre) tail) := rfl
    rw [unf]
    have pm : ∀ (y : ℕ) (l : List ℕ), (y :: l).Perm (pre ++ post) → (x0 :: y :: l).Perm (pre ++ x0 :: post) :=
      fun y l hp => (hp.cons x0).trans List.perm_middle.symm
    by_cases hax : a = x0
    · subst hax
      have hb' : b ∈ post := (List.mem_cons.mp hb).resolve_left (Ne.symm hab)
      exact inner_hit flt e thr ws a b Q post acc pre _ hb' hacc
        (fun sk' rest' acc' hp hk => cb a b sk' rest' acc' (Or.inl ⟨rfl, rfl⟩) (pm b _ hp) hk)
    · by_cases hbx : b = x0
      · subst hbx
        have ha' : a ∈ post := (List.mem_cons.mp ha).resolve_left hax
        exact inner_hit flt e thr ws b a Q post acc pre _ ha' hacc
          (fun sk' rest' acc' hp hk => cb b a sk' rest' acc' (Or.inr ⟨rfl, rfl⟩) (pm a _ hp) hk)
      · have ha' : a ∈ post := (List.mem_cons.mp ha).resolve_left hax
        have hb' : b ∈ post := (List.mem_cons.mp hb).resolve_left hbx
        obtain ⟨c, hq, hc⟩ := ih (Nat.lor acc (Nat.xor (Nat.shiftRight x0 nP) x0)) (x0 :: pre) tail ha' hb' hab
          (accOK_cons hacc x0) (fun x y sk' rest' acc' hxy hp hk => cb x y sk' rest' acc' hxy
            (hp.trans (by simpa using (List.perm_middle (a := x0) (l₁ := pre) (l₂ := post)).symm)) hk)
        exact ⟨c, hq, innerK_mono flt e thr ws x0 post acc pre _ hc⟩

def goodKid (e z x y : ℕ) (ws : List ℕ) (kx ky : Bool) (c : ℕ × List ℕ) : Prop :=
  ∃ kept : List ℕ, c = (e - kx.toNat - ky.toNat, z :: kept) ∧ kept.Nodup ∧
    (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ kx = true) ∨ (v = y ∧ ky = true)) ∧
    kept.length + 2 = ws.length + kx.toNat + ky.toNat

set_option maxRecDepth 100000 in
theorem pair_hit (e thr x y z : ℕ) (ws sk rest : List ℕ) (acc : ℕ) (kx ky : Bool)
    (hz : z ∈ opsN x y) (hthr : thr ≤ z) (hfresh : z ∉ ws) (hnd : ws.Nodup)
    (hperm : (x :: y :: (sk ++ rest)).Perm ws) (hacc : accOK acc sk)
    (slack : kx.toNat + ky.toNat ≤ e)
    (cut : ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ kx = true) ∨ (v = y ∧ ky = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true)
    (r : List ℕ) (hr : r.Perm (sk ++ rest)) :
    (Nat.beq (dz (Nat.lor acc (cutN rest)) z) 0 = true ∨ 0 < e) ∧
    ∃ c, goodKid e z x y ws kx ky c ∧
      ∀ tail', c ∈ pairK e thr x y ws r (Nat.lor acc (cutN rest)) tail' := by
  have hperm' : (x :: y :: r).Perm ws := ((hr.cons y).cons x).trans hperm
  have nd := hperm'.nodup_iff.mpr hnd
  have mem : ∀ v, v ∈ ws ↔ v = x ∨ v = y ∨ v ∈ r := by
    intro v; rw [← hperm'.mem_iff]; simp
  have hxy : x ≠ y := by
    intro h; subst h; simp at nd
  have hxr : x ∉ r := by
    intro h; simp only [List.nodup_cons, List.mem_cons, not_or] at nd; exact nd.1.2 h
  have hyr : y ∉ r := by
    intro h; simp only [List.nodup_cons, List.mem_cons, not_or] at nd; exact nd.2.1 h
  have ndr : r.Nodup := by
    simp only [List.nodup_cons] at nd; exact nd.2.2
  have len : ws.length = r.length + 2 := by
    rw [← hperm'.length_eq]; simp
  have rmem : ∀ v, v ∈ r ↔ v ∈ ws ∧ v ≠ x ∧ v ≠ y := by
    intro v
    rw [mem]
    constructor
    · intro h; exact ⟨Or.inr (Or.inr h), fun e => hxr (e ▸ h), fun e => hyr (e ▸ h)⟩
    · rintro ⟨h | h | h, h1, h2⟩
      · exact absurd h h1
      · exact absurd h h2
      · exact h
  have basebit : ∀ (extra : ℕ) (kept : List ℕ),
      (∀ v ∈ kept, v ∈ r ∨ ∀ i, (sp v).testBit i = true → extra.testBit i = true) →
      (∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) →
      Nat.beq (dz (Nat.lor (Nat.lor acc (cutN rest)) extra) z) 0 = true := by
    intro extra kept hk hc
    apply pass_of
    · intro i hi
      obtain ⟨w, hw, hb⟩ := hc i hi
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inl hb
      · right
        change ((acc ||| cutN rest) ||| extra).testBit i = true
        rw [Nat.testBit_or, Nat.testBit_or, Bool.or_eq_true, Bool.or_eq_true]
        rcases hk w hw with h | h
        · rcases List.mem_append.mp (hr.mem_iff.mp h) with h | h
          · exact Or.inl (Or.inl (hacc.2 w h i hb))
          · exact Or.inl (Or.inr ((cutN_bit rest i).mpr ⟨w, h, hb⟩))
        · exact Or.inr (h i hb)
    · intro i h1 h2
      change ((acc ||| cutN rest) ||| extra).testBit i = true
      rw [Nat.testBit_or, Nat.testBit_or, hacc.1 i h1 h2]
      rfl
  have base0 : ∀ kept : List ℕ, (∀ v ∈ kept, v ∈ r) →
      (∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) →
      Nat.beq (dz (Nat.lor acc (cutN rest)) z) 0 = true := by
    intro kept hk hc
    have h := basebit 0 kept (fun v hv => Or.inl (hk v hv)) hc
    have e0 : Nat.lor (Nat.lor acc (cutN rest)) 0 = Nat.lor acc (cutN rest) := Nat.or_zero _
    rw [e0] at h
    exact h
  cases kx <;> cases ky
  · have kmem : ∀ v, v ∈ r ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ false = true) ∨ (v = y ∧ false = true) := by
      intro v; rw [rmem]; simp
    have hp := base0 r (fun v hv => hv) (cut _ kmem)
    refine ⟨Or.inl hp, (e, z :: r), ⟨r, rfl, ndr, kmem, by simp [len]⟩, fun tail' => ?_⟩
    cases e with
    | zero => exact pairZ_hit thr x y z ws r _ tail' hz hthr hfresh hp
    | succ e1 =>
      change _ ∈ pairKS _ thr x y ws r (Nat.lor acc (cutN rest)) tail'
      apply pairKS_hit _ _ _ _ _ _ _ _ _ hz
      intro t
      rw [cand_eq _ _ _ _ _ _ _ _ _ hthr hfresh]
      exact cand0_none _ _ _ _ _ _ _ hp
  · obtain ⟨e1, rfl⟩ : ∃ e1, e = e1 + 1 := ⟨e - 1, by simp at slack; omega⟩
    have kmem : ∀ v, v ∈ y :: r ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ false = true) ∨ (v = y ∧ true = true) := by
      intro v; rw [List.mem_cons, rmem]; simp; tauto
    have hp := basebit (sp y) (y :: r)
      (fun v hv => by
        rcases List.mem_cons.mp hv with rfl | hv
        · exact Or.inr (fun i h => h)
        · exact Or.inl hv) (cut _ kmem)
    refine ⟨Or.inr (by omega), (e1, z :: y :: r),
      ⟨y :: r, by simp, List.nodup_cons.mpr ⟨hyr, ndr⟩, kmem, by simp [len]⟩, fun tail' => ?_⟩
    change _ ∈ pairKS _ thr x y ws r (Nat.lor acc (cutN rest)) tail'
    apply pairKS_hit _ _ _ _ _ _ _ _ _ hz
    intro t
    rw [cand_eq _ _ _ _ _ _ _ _ _ hthr hfresh]
    exact cand0_b _ _ _ _ _ _ _ hp
  · obtain ⟨e1, rfl⟩ : ∃ e1, e = e1 + 1 := ⟨e - 1, by simp at slack; omega⟩
    have kmem : ∀ v, v ∈ x :: r ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ true = true) ∨ (v = y ∧ false = true) := by
      intro v; rw [List.mem_cons, rmem]; simp; tauto
    have hp := basebit (sp x) (x :: r)
      (fun v hv => by
        rcases List.mem_cons.mp hv with rfl | hv
        · exact Or.inr (fun i h => h)
        · exact Or.inl hv) (cut _ kmem)
    refine ⟨Or.inr (by omega), (e1, z :: x :: r),
      ⟨x :: r, by simp, List.nodup_cons.mpr ⟨hxr, ndr⟩, kmem, by simp [len]⟩, fun tail' => ?_⟩
    change _ ∈ pairKS _ thr x y ws r (Nat.lor acc (cutN rest)) tail'
    apply pairKS_hit _ _ _ _ _ _ _ _ _ hz
    intro t
    rw [cand_eq _ _ _ _ _ _ _ _ _ hthr hfresh]
    exact cand0_a _ _ _ _ _ _ _ hp
  · obtain ⟨e2, rfl⟩ : ∃ e2, e = e2 + 2 := ⟨e - 2, by simp at slack; omega⟩
    have kmem : ∀ v, v ∈ x :: y :: r ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ true = true) ∨ (v = y ∧ true = true) := by
      intro v; rw [List.mem_cons, List.mem_cons, rmem]; simp; tauto
    refine ⟨Or.inr (by omega), (e2, z :: x :: y :: r),
      ⟨x :: y :: r, by simp, nd, kmem, by simp [len]⟩, fun tail' => ?_⟩
    change _ ∈ pairKS _ thr x y ws r (Nat.lor acc (cutN rest)) tail'
    apply pairKS_hit _ _ _ _ _ _ _ _ _ hz
    intro t
    rw [cand_eq _ _ _ _ _ _ _ _ _ hthr hfresh]
    exact cand0_ab _ _ _ _ _ _ _


def run (t : ℕ) : Finset ℕ → List (ℕ × ℕ × ℕ) → Prop
  | av, [] => t ∈ av
  | av, g :: L => g.1 ∈ av ∧ g.2.1 ∈ av ∧ g.1 ≠ g.2.1 ∧ g.2.2 ∈ opsN g.1 g.2.1 ∧ run t (insert g.2.2 av) L

def used (t : ℕ) : List (ℕ × ℕ × ℕ) → ℕ → Prop
  | [], v => v = t
  | g :: L, v => v = g.1 ∨ v = g.2.1 ∨ used t L v

def normal : Finset ℕ → List (ℕ × ℕ × ℕ) → Prop
  | _, [] => True
  | av, g :: L => (∀ g2 ∈ L.head?, ¬(g2.1 ∈ av ∧ g2.2.1 ∈ av ∧ g2.2.2 < g.2.2)) ∧ normal (insert g.2.2 av) L

def tight (t : ℕ) (av : Finset ℕ) (L : List (ℕ × ℕ × ℕ)) : Prop :=
  run t av L ∧ ∀ L', run t av L' → L.length ≤ L'.length

set_option maxRecDepth 100000 in
theorem run_drop (t z : ℕ) : ∀ (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ), run t (insert z av) L → ¬ used t L z →
    run t av L := by
  intro L
  induction L with
  | nil =>
    intro av h hu
    exact (Finset.mem_insert.mp h).resolve_left (fun e => hu e.symm)
  | cons g L ih =>
    intro av h hu
    obtain ⟨h1, h2, h3, h4, h5⟩ := h
    have u1 : z ≠ g.1 := fun e => hu (Or.inl e)
    have u2 : z ≠ g.2.1 := fun e => hu (Or.inr (Or.inl e))
    refine ⟨(Finset.mem_insert.mp h1).resolve_left (Ne.symm u1), (Finset.mem_insert.mp h2).resolve_left (Ne.symm u2),
      h3, h4, ih _ ?_ (fun u => hu (Or.inr (Or.inr u)))⟩
    rw [Finset.insert_comm]
    exact h5

set_option maxRecDepth 100000 in
theorem tight_tail {t : ℕ} {av : Finset ℕ} {g : ℕ × ℕ × ℕ} {L : List (ℕ × ℕ × ℕ)} (h : tight t av (g :: L)) :
    tight t (insert g.2.2 av) L := by
  refine ⟨h.1.2.2.2.2, fun L' h' => ?_⟩
  have := h.2 (g :: L') ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2.1, h'⟩
  simpa using this

set_option maxRecDepth 100000 in
theorem tight_fresh {t : ℕ} {av : Finset ℕ} {g : ℕ × ℕ × ℕ} {L : List (ℕ × ℕ × ℕ)} (h : tight t av (g :: L)) :
    g.2.2 ∉ av := by
  intro hm
  have hr : run t av L := by
    have := h.1.2.2.2.2
    rwa [Finset.insert_eq_of_mem hm] at this
  have := h.2 L hr
  simp at this

set_option maxRecDepth 100000 in
theorem tight_used {t : ℕ} {av : Finset ℕ} {g : ℕ × ℕ × ℕ} {L : List (ℕ × ℕ × ℕ)} (h : tight t av (g :: L)) :
    used t L g.2.2 := by
  by_contra hu
  have := h.2 L (run_drop t g.2.2 L av h.1.2.2.2.2 hu)
  simp at this

set_option maxRecDepth 100000 in
theorem exists_tight {t : ℕ} {av : Finset ℕ} {L : List (ℕ × ℕ × ℕ)} (h : run t av L) :
    ∃ L0, tight t av L0 ∧ L0.length ≤ L.length := by
  classical
  have ex : ∃ n, ∃ L' : List (ℕ × ℕ × ℕ), L'.length = n ∧ run t av L' := ⟨_, L, rfl, h⟩
  obtain ⟨L0, hl, hr⟩ := Nat.find_spec ex
  refine ⟨L0, ⟨hr, fun L' h' => ?_⟩, ?_⟩
  · rw [hl]; exact Nat.find_min' ex ⟨L', rfl, h'⟩
  · rw [hl]; exact Nat.find_min' ex ⟨L, rfl, h⟩

set_option maxRecDepth 100000 in
theorem ins_normal (t : ℕ) : ∀ (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ) (g : ℕ × ℕ × ℕ), g.1 ∈ av → g.2.1 ∈ av →
    g.1 ≠ g.2.1 → g.2.2 ∈ opsN g.1 g.2.1 → run t (insert g.2.2 av) L → normal (insert g.2.2 av) L →
    ∃ L' : List (ℕ × ℕ × ℕ), L'.length = L.length + 1 ∧ run t av L' ∧ normal av L' ∧
      (L'.head? = some g ∨ L'.head? = L.head?) := by
  intro L
  induction L with
  | nil =>
    intro av g h1 h2 h3 h4 hr hn
    exact ⟨[g], rfl, ⟨h1, h2, h3, h4, hr⟩, ⟨by simp, trivial⟩, Or.inl rfl⟩
  | cons g2 Lt ih =>
    intro av g h1 h2 h3 h4 hr hn
    obtain ⟨r1, r2, r3, r4, r5⟩ := hr
    obtain ⟨n1, n2⟩ := hn
    by_cases c : g2.1 ∈ av ∧ g2.2.1 ∈ av ∧ g2.2.2 < g.2.2
    · have r5' : run t (insert g.2.2 (insert g2.2.2 av)) Lt := by rw [Finset.insert_comm]; exact r5
      have n2' : normal (insert g.2.2 (insert g2.2.2 av)) Lt := by rw [Finset.insert_comm]; exact n2
      obtain ⟨L'', hl, hr'', hn'', hh⟩ := ih (insert g2.2.2 av) g (Finset.mem_insert_of_mem h1)
        (Finset.mem_insert_of_mem h2) h3 h4 r5' n2'
      refine ⟨g2 :: L'', by simp [hl], ⟨c.1, c.2.1, r3, r4, hr''⟩, ⟨?_, hn''⟩, Or.inr rfl⟩
      intro g3 hg3
      rcases hh with hh | hh
      · rw [hh] at hg3
        simp only [Option.mem_def, Option.some.injEq] at hg3
        subst hg3
        exact fun hx => absurd hx.2.2 (Nat.lt_asymm c.2.2)
      · rw [hh] at hg3
        have := n1 g3 hg3
        exact fun hx => this ⟨Finset.mem_insert_of_mem hx.1, Finset.mem_insert_of_mem hx.2.1, hx.2.2⟩
    · refine ⟨g :: g2 :: Lt, rfl, ⟨h1, h2, h3, h4, r1, r2, r3, r4, r5⟩, ⟨?_, n1, n2⟩, Or.inl rfl⟩
      intro g3 hg3
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hg3
      subst hg3
      exact c

set_option maxRecDepth 100000 in
theorem sort_normal (t : ℕ) : ∀ (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ), run t av L →
    ∃ L' : List (ℕ × ℕ × ℕ), L'.length = L.length ∧ run t av L' ∧ normal av L' := by
  intro L
  induction L with
  | nil => intro av h; exact ⟨[], rfl, h, trivial⟩
  | cons g L ih =>
    intro av h
    obtain ⟨L1, l1, r1, n1⟩ := ih _ h.2.2.2.2
    obtain ⟨L', l', r', n', _⟩ := ins_normal t L1 av g h.1 h.2.1 h.2.2.1 h.2.2.2.1 r1 n1
    exact ⟨L', by simp [l', l1], r', n'⟩

set_option maxRecDepth 100000 in
theorem run_sep (t : ℕ) (D : ℕ → Prop) (hd : D t) (hops : ∀ a b z, z ∈ opsN a b → D z → D a ∨ D b) :
    ∀ (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ), run t av L → ∃ w ∈ av, used t L w ∧ D w := by
  intro L
  induction L with
  | nil => intro av h; exact ⟨t, h, rfl, hd⟩
  | cons g L ih =>
    intro av h
    obtain ⟨w, hw, hu, hD⟩ := ih _ h.2.2.2.2
    rcases Finset.mem_insert.mp hw with rfl | hw
    · rcases hops _ _ _ h.2.2.2.1 hD with d | d
      · exact ⟨g.1, h.1, Or.inl rfl, d⟩
      · exact ⟨g.2.1, h.2.1, Or.inr (Or.inl rfl), d⟩
    · exact ⟨w, hw, Or.inr (Or.inr hu), hD⟩

set_option maxRecDepth 100000 in
theorem ops_sep (i a b z : ℕ) (hz : z ∈ opsN a b) (h : (sp z).testBit i = true) :
    (sp a).testBit i = true ∨ (sp b).testBit i = true := by
  have e1 : ∀ x y : ℕ, Nat.land x y = x &&& y := fun _ _ => rfl
  have e2 : ∀ x y : ℕ, Nat.lor x y = x ||| y := fun _ _ => rfl
  have e3 : ∀ x y : ℕ, Nat.xor x y = x ^^^ y := fun _ _ => rfl
  simp only [opsN, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> revert h <;>
    simp only [sp_bit, e1, e2, e3, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit (nP + i) <;> cases a.testBit i <;> cases b.testBit (nP + i) <;> cases b.testBit i <;> decide

set_option maxRecDepth 100000 in
theorem single_of {t : ℕ} {ws : List ℕ} (hn : ws.Nodup) (ht : t ∈ ws) (h : ∀ v ∈ ws, v = t) : ws = [t] := by
  have sub : ws.toFinset ⊆ {t} := by
    intro v hv
    exact Finset.mem_singleton.mpr (h v (List.mem_toFinset.mp hv))
  have c := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup hn, Finset.card_singleton] at c
  match ws, ht, h, c with
  | [w], _, h, _ => rw [h w (by simp)]
  | w :: w2 :: l, _, _, c => simp at c

set_option maxRecDepth 100000 in
theorem short_of {a b : ℕ} {ws : List ℕ} (ka kb : Bool) (hn : ws.Nodup)
    (h : ∀ v ∈ ws, (v = a ∧ ka = false) ∨ (v = b ∧ kb = false)) : ws.length + ka.toNat + kb.toNat ≤ 2 := by
  have sub : ws.toFinset ⊆ (if ka = false then {a} else ∅) ∪ (if kb = false then {b} else ∅) := by
    intro v hv
    rcases h v (List.mem_toFinset.mp hv) with ⟨rfl, k⟩ | ⟨rfl, k⟩ <;> simp [k]
  have c := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup hn] at c
  have u := Finset.card_union_le (if ka = false then ({a} : Finset ℕ) else ∅) (if kb = false then {b} else ∅)
  cases ka <;> cases kb <;> simp at c u ⊢ <;> omega

set_option maxRecDepth 100000 in
theorem frontier_card (t : ℕ) : ∀ (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ) (ws : List ℕ), tight t av L → ws.Nodup →
    (∀ v ∈ ws, v ∈ av ∧ used t L v) → ws.length ≤ L.length + 1 := by
  intro L
  induction L with
  | nil =>
    intro av ws _ hn hm
    cases ws with
    | nil => simp
    | cons w l =>
      have e := single_of hn ((hm w (by simp)).2 ▸ List.mem_cons_self) (fun v hv => (hm v hv).2)
      rw [e]; simp
  | cons g L ih =>
    intro av ws ht hn hm
    classical
    have hz : g.2.2 ∉ ws := fun h => tight_fresh ht (hm _ h).1
    have c1 := ih (insert g.2.2 av) (g.2.2 :: ws.filter (fun v => decide (used t L v))) (tight_tail ht)
      (List.nodup_cons.mpr ⟨fun h => hz (List.mem_filter.mp h).1, hn.filter _⟩)
      (by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨Finset.mem_insert_self _ _, tight_used ht⟩
        · have := List.mem_filter.mp hv
          exact ⟨Finset.mem_insert_of_mem (hm v this.1).1, of_decide_eq_true this.2⟩)
    have c2 := short_of (a := g.1) (b := g.2.1) false false
      (hn.filter (fun v => !decide (used t L v)))
      (by
        intro v hv
        have hv' := List.mem_filter.mp hv
        have nu : ¬ used t L v := by simpa using hv'.2
        rcases (hm v hv'.1).2 with e | e | e
        · exact Or.inl ⟨e, rfl⟩
        · exact Or.inr ⟨e, rfl⟩
        · exact absurd e nu)
    have c3 := List.length_eq_length_filter_add (l := ws) (fun v => decide (used t L v))
    simp only [List.length_cons, Bool.toNat_false] at c1 c2 ⊢
    omega

set_option maxRecDepth 100000 in
theorem step_child (t : ℕ) (hD : ∀ i < nP, (sp t).testBit i = true) (av : Finset ℕ) (g : ℕ × ℕ × ℕ)
    (L' : List (ℕ × ℕ × ℕ)) (ws : List ℕ) (e k : ℕ) (ht : tight t av (g :: L')) (hl : L'.length ≤ k)
    (hn : ws.Nodup) (hm : ∀ v, v ∈ ws ↔ v ∈ av ∧ used t (g :: L') v) (he : e + ws.length = k + 2) :
    ∃ ka kb : Bool, ka.toNat + kb.toNat ≤ e ∧ g.1 ∈ ws ∧ g.2.1 ∈ ws ∧ g.2.2 ∉ ws ∧
      ∀ kept : List ℕ,
        (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ g.1 ∧ v ≠ g.2.1) ∨ (v = g.1 ∧ ka = true) ∨ (v = g.2.1 ∧ kb = true)) →
        (∀ i < nP, ∃ w ∈ g.2.2 :: kept, (sp w).testBit i = true) ∧
        (kept.Nodup → (g.2.2 :: kept).Nodup) ∧
        (∀ v, v ∈ g.2.2 :: kept ↔ v ∈ insert g.2.2 av ∧ used t L' v) := by
  classical
  have ha : g.1 ∈ ws := (hm _).mpr ⟨ht.1.1, Or.inl rfl⟩
  have hb : g.2.1 ∈ ws := (hm _).mpr ⟨ht.1.2.1, Or.inr (Or.inl rfl)⟩
  have hz : g.2.2 ∉ ws := fun h => tight_fresh ht ((hm _).mp h).1
  refine ⟨decide (used t L' g.1), decide (used t L' g.2.1), ?_, ha, hb, hz, ?_⟩
  · have c1 := frontier_card t L' (insert g.2.2 av) (g.2.2 :: ws.filter (fun v => decide (used t L' v)))
      (tight_tail ht) (List.nodup_cons.mpr ⟨fun h => hz (List.mem_filter.mp h).1, hn.filter _⟩)
      (by
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact ⟨Finset.mem_insert_self _ _, tight_used ht⟩
        · have := List.mem_filter.mp hv
          exact ⟨Finset.mem_insert_of_mem ((hm v).mp this.1).1, of_decide_eq_true this.2⟩)
    have c2 := short_of (a := g.1) (b := g.2.1) (decide (used t L' g.1)) (decide (used t L' g.2.1))
      (hn.filter (fun v => !decide (used t L' v)))
      (by
        intro v hv
        have hv' := List.mem_filter.mp hv
        have nu : ¬ used t L' v := by simpa using hv'.2
        rcases ((hm v).mp hv'.1).2 with e | e | e
        · exact Or.inl ⟨e, by rw [← e]; simpa using nu⟩
        · exact Or.inr ⟨e, by rw [← e]; simpa using nu⟩
        · exact absurd e nu)
    have c3 := List.length_eq_length_filter_add (l := ws) (fun v => decide (used t L' v))
    simp only [List.length_cons] at c1
    omega
  · intro kept hk
    have key : ∀ v, v ∈ kept ↔ v ∈ av ∧ used t L' v := by
      intro v
      rw [hk v]
      constructor
      · rintro (⟨h1, h2, h3⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
        · have := (hm v).mp h1
          rcases this.2 with e | e | e
          · exact absurd e h2
          · exact absurd e h3
          · exact ⟨this.1, e⟩
        · exact ⟨ht.1.1, of_decide_eq_true h⟩
        · exact ⟨ht.1.2.1, of_decide_eq_true h⟩
      · rintro ⟨h1, h2⟩
        by_cases e1 : v = g.1
        · exact Or.inr (Or.inl ⟨e1, by rw [← e1]; exact decide_eq_true h2⟩)
        · by_cases e2 : v = g.2.1
          · exact Or.inr (Or.inr ⟨e2, by rw [← e2]; exact decide_eq_true h2⟩)
          · exact Or.inl ⟨(hm v).mpr ⟨h1, Or.inr (Or.inr h2)⟩, e1, e2⟩
    have mem : ∀ v, v ∈ g.2.2 :: kept ↔ v ∈ insert g.2.2 av ∧ used t L' v := by
      intro v
      rw [List.mem_cons, key v, Finset.mem_insert]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Or.inl rfl, tight_used ht⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨rfl | h1, h2⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨h1, h2⟩
    refine ⟨fun i hi => ?_, fun hkn => List.nodup_cons.mpr ⟨fun h => tight_fresh ht ((key _).mp h).1, hkn⟩, mem⟩
    obtain ⟨w, hw, hu, hb⟩ := run_sep t (fun w => (sp w).testBit i = true) (hD i hi)
      (fun a b z hz h => ops_sep i a b z hz h) L' _ ht.1.2.2.2.2
    exact ⟨w, (mem w).mpr ⟨hw, hu⟩, hb⟩

set_option maxRecDepth 100000 in
theorem goodKid_swap {e z x y : ℕ} {ws : List ℕ} {kx ky : Bool} {c : ℕ × List ℕ}
    (h : goodKid e z y x ws ky kx c) : goodKid e z x y ws kx ky c := by
  obtain ⟨kept, rfl, h1, h2, h3⟩ := h
  refine ⟨kept, by rw [Nat.sub_right_comm], h1, fun v => (h2 v).trans (by tauto), by omega⟩

set_option maxRecDepth 100000 in
theorem cut_swap {z x y : ℕ} {ws : List ℕ} {kx ky : Bool}
    (cut : ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ kx = true) ∨ (v = y ∧ ky = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) :
    ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ y ∧ v ≠ x) ∨ (v = y ∧ ky = true) ∨ (v = x ∧ kx = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true :=
  fun kept hk => cut kept (fun v => (hk v).trans (by tauto))

set_option maxRecDepth 100000 in
theorem flt0_OK : fltOK flt0 0 := fun a b base z hz hp => flt0_ok a b base z hz (hp.resolve_right (by simp))

set_option maxRecDepth 100000 in
theorem fltT_OK (e : ℕ) : fltOK fltT e := fun _ _ _ _ _ _ => rfl

set_option maxRecDepth 100000 in
theorem pair_cb {e : ℕ} (flt : ℕ → ℕ → ℕ → Bool) (hflt : fltOK flt e) (thr x y z : ℕ) (ws sk rest : List ℕ) (acc : ℕ)
    (kx ky : Bool) (hz : z ∈ opsN x y) (hthr : thr ≤ z) (hfresh : z ∉ ws) (hnd : ws.Nodup)
    (hperm : (x :: y :: (sk ++ rest)).Perm ws) (hacc : accOK acc sk) (slack : kx.toNat + ky.toNat ≤ e)
    (cut : ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ x ∧ v ≠ y) ∨ (v = x ∧ kx = true) ∨ (v = y ∧ ky = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) :
    flt x y (Nat.lor acc (cutN rest)) = true ∧
    ∀ r : List ℕ, r.Perm (sk ++ rest) →
      ∃ c, goodKid e z x y ws kx ky c ∧
        ∀ tail', c ∈ pairK e thr x y ws r (Nat.lor acc (cutN rest)) tail' :=
  ⟨hflt x y _ z hz (pair_hit e thr x y z ws sk rest acc kx ky hz hthr hfresh hnd hperm hacc slack cut (sk ++ rest)
      (List.Perm.refl _)).1,
    fun r hr => (pair_hit e thr x y z ws sk rest acc kx ky hz hthr hfresh hnd hperm hacc slack cut r hr).2⟩

set_option maxRecDepth 100000 in
theorem bit_of_ne (p : ℕ) (hp : p ≠ 0) : ∃ i, p.testBit i = true := by
  by_contra hn
  apply hp
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.zero_testBit]
  cases hb : p.testBit i
  · rfl
  · exact absurd ⟨i, hb⟩ hn

set_option maxRecDepth 100000 in
theorem crossC_wit : ∀ (ws : List ℕ) (p q : ℕ), crossC ws p q = true →
    ∃ i j, p.testBit i = true ∧ q.testBit j = true ∧ ∀ w ∈ ws, w.testBit i = w.testBit (nP + j) := by
  intro ws
  induction ws with
  | nil =>
    intro p q h
    change (Bool.rec (Bool.rec true false (Nat.beq q 0)) false (Nat.beq p 0) : Bool) = true at h
    have hp : p ≠ 0 := by
      intro e
      subst e
      exact Bool.noConfusion (show false = true from h)
    have hq : q ≠ 0 := by
      intro e
      subst e
      cases hb : Nat.beq p 0
      · rw [hb] at h
        exact Bool.noConfusion (show false = true from h)
      · rw [hb] at h
        exact Bool.noConfusion (show false = true from h)
    obtain ⟨i, hi⟩ := bit_of_ne p hp
    obtain ⟨j, hj⟩ := bit_of_ne q hq
    exact ⟨i, j, hi, hj, by simp⟩
  | cons w ws ih =>
    intro p q h
    change (Bool.rec (Bool.rec (Bool.rec (crossC ws (Nat.xor p (Nat.land p w))
      (Nat.xor q (Nat.land q (Nat.shiftRight w nP)))) true (crossC ws (Nat.land p w) (Nat.land q (Nat.shiftRight w nP))))
      false (Nat.beq q 0)) false (Nat.beq p 0) : Bool) = true at h
    cases hp : Nat.beq p 0
    · rw [hp] at h
      cases hq : Nat.beq q 0
      · rw [hq] at h
        cases h1 : crossC ws (Nat.land p w) (Nat.land q (Nat.shiftRight w nP))
        · rw [h1] at h
          have h0 : crossC ws (Nat.xor p (Nat.land p w)) (Nat.xor q (Nat.land q (Nat.shiftRight w nP))) = true := h
          obtain ⟨i, j, pi, qj, hall⟩ := ih _ _ h0
          change (p ^^^ (p &&& w)).testBit i = true at pi
          change (q ^^^ (q &&& (w >>> nP))).testBit j = true at qj
          rw [Nat.testBit_xor, Nat.testBit_and] at pi
          rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight] at qj
          have pi' : p.testBit i = true ∧ w.testBit i = false := by
            revert pi; cases p.testBit i <;> cases w.testBit i <;> decide
          have qj' : q.testBit j = true ∧ w.testBit (nP + j) = false := by
            revert qj; cases q.testBit j <;> cases w.testBit (nP + j) <;> decide
          refine ⟨i, j, pi'.1, qj'.1, fun v hv => ?_⟩
          rcases List.mem_cons.mp hv with ev | hv
          · rw [ev, pi'.2, qj'.2]
          · exact hall v hv
        · obtain ⟨i, j, pi, qj, hall⟩ := ih _ _ h1
          change (p &&& w).testBit i = true at pi
          change (q &&& (w >>> nP)).testBit j = true at qj
          rw [Nat.testBit_and, Bool.and_eq_true] at pi
          rw [Nat.testBit_and, Nat.testBit_shiftRight, Bool.and_eq_true] at qj
          refine ⟨i, j, pi.1, qj.1, fun v hv => ?_⟩
          rcases List.mem_cons.mp hv with ev | hv
          · rw [ev, pi.2, qj.2]
          · exact hall v hv
      · rw [hq] at h
        exact Bool.noConfusion (show false = true from h)
    · rw [hp] at h
      exact Bool.noConfusion (show false = true from h)

set_option maxRecDepth 100000 in
theorem ops_diff (i j a b z : ℕ) (hz : z ∈ opsN a b) (h : z.testBit i ≠ z.testBit j) :
    a.testBit i ≠ a.testBit j ∨ b.testBit i ≠ b.testBit j := by
  have e1 : ∀ x y : ℕ, Nat.land x y = x &&& y := fun _ _ => rfl
  have e2 : ∀ x y : ℕ, Nat.lor x y = x ||| y := fun _ _ => rfl
  have e3 : ∀ x y : ℕ, Nat.xor x y = x ^^^ y := fun _ _ => rfl
  simp only [opsN, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> revert h <;>
    simp only [e1, e2, e3, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit i <;> cases a.testBit j <;> cases b.testBit i <;> cases b.testBit j <;> decide

set_option maxRecDepth 100000 in
theorem coll_ok (c t : ℕ) (ht : t = hiM ∨ t = fullM) (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ) (ws : List ℕ)
    (hr : run t av L) (hm : ∀ v, v ∈ ws ↔ v ∈ av ∧ used t L v) : collOK c ws = true := by
  cases c with
  | zero => rfl
  | succ c =>
    change (Bool.rec true false (crossC ws fullM fullM) : Bool) = true
    cases hc : crossC ws fullM fullM
    · rfl
    · exfalso
      obtain ⟨i, j, pi, qj, hall⟩ := crossC_wit ws fullM fullM hc
      have hi : i < nP := by
        rw [show fullM = 2 ^ nP - 1 from rfl, Nat.testBit_two_pow_sub_one] at pi
        exact of_decide_eq_true pi
      have hj : j < nP := by
        rw [show fullM = 2 ^ nP - 1 from rfl, Nat.testBit_two_pow_sub_one] at qj
        exact of_decide_eq_true qj
      have hd : t.testBit i ≠ t.testBit (nP + j) := by
        rcases ht with rfl | rfl
        · rw [hiM_bit (nP + j) (Nat.le_add_right _ _) (by omega),
            show hiM = (2 ^ nP - 1) <<< nP from rfl, Nat.testBit_shiftLeft]
          have : ¬ (i ≥ nP) := by omega
          simp [this]
        · rw [show fullM = 2 ^ nP - 1 from rfl, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
          have : ¬ (nP + j < nP) := by omega
          simp [hi, this]
      obtain ⟨w, hw, hu, hD⟩ := run_sep t (fun w => w.testBit i ≠ w.testBit (nP + j)) hd
        (fun a b z hz h => ops_diff i (nP + j) a b z hz h) L av hr
      exact hD (hall w ((hm w).mpr ⟨hw, hu⟩))

set_option maxRecDepth 100000 in
theorem kidsG_hit (flt : ℕ → ℕ → ℕ → Bool) (e : ℕ) (hflt : fltOK flt e) (h : ℕ) (tl : List ℕ) (a b z : ℕ)
    (ka kb : Bool) (hn : (h :: tl).Nodup)
    (ha : a ∈ h :: tl) (hb : b ∈ h :: tl) (hab : a ≠ b) (hz : z ∈ opsN a b)
    (ord : a = h ∨ b = h ∨ h ≤ z) (fresh : z ∉ h :: tl) (slack : ka.toNat + kb.toNat ≤ e)
    (cut : ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ h :: tl ∧ v ≠ a ∧ v ≠ b) ∨ (v = a ∧ ka = true) ∨ (v = b ∧ kb = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) :
    ∃ c, goodKid e z a b (h :: tl) ka kb c ∧ c ∈ kidsG flt e h tl (h :: tl) := by
  unfold kidsG
  by_cases hah : a = h
  · subst hah
    have hb' : b ∈ tl := (List.mem_cons.mp hb).resolve_left (Ne.symm hab)
    exact inner_hit flt e 0 (a :: tl) a b _ tl hiM [] _ hb' accOK_nil
      (fun sk' rest' acc' hp hk => pair_cb flt hflt 0 a b z (a :: tl) sk' rest' acc' ka kb hz (Nat.zero_le _)
        fresh hn (by simpa using hp.cons a) hk slack cut)
  · by_cases hbh : b = h
    · subst hbh
      have ha' : a ∈ tl := (List.mem_cons.mp ha).resolve_left hah
      obtain ⟨c, hq, hc⟩ := inner_hit flt e 0 (b :: tl) b a (goodKid e z b a (b :: tl) kb ka) tl hiM [] _ ha'
        accOK_nil
        (fun sk' rest' acc' hp hk => pair_cb flt hflt 0 b a z (b :: tl) sk' rest' acc' kb ka (opsN_swap hz)
          (Nat.zero_le _) fresh hn (by simpa using hp.cons b) hk (by omega) (cut_swap cut))
      exact ⟨c, goodKid_swap hq, hc⟩
    · have ha' : a ∈ tl := (List.mem_cons.mp ha).resolve_left hah
      have hb' : b ∈ tl := (List.mem_cons.mp hb).resolve_left hbh
      have hz' : h ≤ z := by
        rcases ord with o | o | o
        · exact absurd o hah
        · exact absurd o hbh
        · exact o
      obtain ⟨c, hq, hc⟩ := outer_hit flt e h (h :: tl) a b (goodKid e z a b (h :: tl) ka kb) tl
        (Nat.lor hiM (Nat.xor (Nat.shiftRight h nP) h)) [h] [] ha' hb' hab (accOK_cons accOK_nil h)
        (fun x y sk' rest' acc' hxy hp hk => by
          rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact pair_cb flt hflt h x y z (h :: tl) sk' rest' acc' ka kb hz hz' fresh hn (by simpa using hp) hk
              slack cut
          · obtain ⟨f1, hall⟩ := pair_cb flt hflt h x y z (h :: tl) sk' rest' acc' kb ka (opsN_swap hz) hz'
              fresh hn (by simpa using hp) hk (by omega) (cut_swap cut)
            exact ⟨f1, fun r hr => by
              obtain ⟨c, hq, hc⟩ := hall r hr
              exact ⟨c, goodKid_swap hq, hc⟩⟩)
      exact ⟨c, hq, innerK_mono flt e 0 (h :: tl) h tl hiM [] _ hc⟩

set_option maxRecDepth 100000 in
theorem kids_hit (e h : ℕ) (tl : List ℕ) (a b z : ℕ) (ka kb : Bool) (hn : (h :: tl).Nodup)
    (ha : a ∈ h :: tl) (hb : b ∈ h :: tl) (hab : a ≠ b) (hz : z ∈ opsN a b)
    (ord : a = h ∨ b = h ∨ h ≤ z) (fresh : z ∉ h :: tl) (slack : ka.toNat + kb.toNat ≤ e)
    (cut : ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ h :: tl ∧ v ≠ a ∧ v ≠ b) ∨ (v = a ∧ ka = true) ∨ (v = b ∧ kb = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) :
    ∃ c, goodKid e z a b (h :: tl) ka kb c ∧ c ∈ kids e (h :: tl) := by
  cases e with
  | zero => exact kidsG_hit flt0 0 flt0_OK h tl a b z ka kb hn ha hb hab hz ord fresh slack cut
  | succ e1 =>
    obtain ⟨c, ⟨kept, rfl, hkn, hkm, hkl⟩, hc⟩ :=
      kidsG_hit fltT (e1 + 1) (fltT_OK _) h tl a b z ka kb hn ha hb hab hz ord fresh slack cut
    obtain ⟨kept', hp, hm⟩ := canonMap_hit _ _ _ _ hc
    exact ⟨_, ⟨kept', rfl, hp.nodup_iff.mpr hkn, fun v => hp.mem_iff.trans (hkm v), by rw [hp.length_eq]; exact hkl⟩, hm⟩

set_option maxRecDepth 100000 in
theorem rootRaw_hit (flt : ℕ → ℕ → ℕ → Bool) (e : ℕ) (hflt : fltOK flt e) (ws : List ℕ) (a b z : ℕ) (ka kb : Bool)
    (hn : ws.Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a ≠ b) (hz : z ∈ opsN a b)
    (fresh : z ∉ ws) (slack : ka.toNat + kb.toNat ≤ e)
    (cut : ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ a ∧ v ≠ b) ∨ (v = a ∧ ka = true) ∨ (v = b ∧ kb = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) :
    ∃ c, goodKid e z a b ws ka kb c ∧ c ∈ outerK flt e 0 ws ws hiM [] [] := by
  exact outer_hit flt e 0 ws a b (goodKid e z a b ws ka kb) ws hiM [] [] ha hb hab accOK_nil
    (fun x y sk' rest' acc' hxy hp hk => by
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact pair_cb flt hflt 0 x y z ws sk' rest' acc' ka kb hz (Nat.zero_le _) fresh hn (by simpa using hp) hk
          slack cut
      · obtain ⟨f1, hall⟩ := pair_cb flt hflt 0 x y z ws sk' rest' acc' kb ka (opsN_swap hz) (Nat.zero_le _)
          fresh hn (by simpa using hp) hk (by omega) (cut_swap cut)
        exact ⟨f1, fun r hr => by
          obtain ⟨c, hq, hc⟩ := hall r hr
          exact ⟨c, goodKid_swap hq, hc⟩⟩)

set_option maxRecDepth 100000 in
theorem kidsRoot_hit (e : ℕ) (ws : List ℕ) (a b z : ℕ) (ka kb : Bool) (hn : ws.Nodup)
    (ha : a ∈ ws) (hb : b ∈ ws) (hab : a ≠ b) (hz : z ∈ opsN a b)
    (fresh : z ∉ ws) (slack : ka.toNat + kb.toNat ≤ e)
    (cut : ∀ kept : List ℕ,
      (∀ v, v ∈ kept ↔ (v ∈ ws ∧ v ≠ a ∧ v ≠ b) ∨ (v = a ∧ ka = true) ∨ (v = b ∧ kb = true)) →
      ∀ i < nP, ∃ w ∈ z :: kept, (sp w).testBit i = true) :
    ∃ c, goodKid e z a b ws ka kb c ∧ c ∈ kidsRoot e ws := by
  have key : ∃ flt : ℕ → ℕ → ℕ → Bool, fltOK flt e ∧ kidsRoot e ws = canonMap (outerK flt e 0 ws ws hiM [] []) := by
    cases e with
    | zero => exact ⟨flt0, flt0_OK, rfl⟩
    | succ e1 => exact ⟨fltT, fltT_OK _, rfl⟩
  obtain ⟨flt, hflt, hk⟩ := key
  rw [hk]
  obtain ⟨c, ⟨kept, rfl, hkn, hkm, hkl⟩, hc⟩ := rootRaw_hit flt e hflt ws a b z ka kb hn ha hb hab hz fresh slack cut
  obtain ⟨kept', hp, hm⟩ := canonMap_hit _ _ _ _ hc
  exact ⟨_, ⟨kept', rfl, hp.nodup_iff.mpr hkn, fun v => hp.mem_iff.trans (hkm v), by rw [hp.length_eq]; exact hkl⟩, hm⟩

set_option maxRecDepth 100000 in
theorem isGoal_single (t : ℕ) (h : t = hiM ∨ t = fullM) : isGoal [t] = true := by
  change (Bool.rec (Nat.beq t fullM) true (Nat.beq t hiM) : Bool) = true
  rcases h with rfl | rfl
  · rw [Nat.beq_refl]
  · rw [Nat.beq_refl]; cases Nat.beq fullM hiM <;> rfl

set_option maxRecDepth 100000 in
theorem anyK_of_mem (f : ℕ → List ℕ → Bool) : ∀ (l : List (ℕ × List ℕ)) (c : ℕ × List ℕ), c ∈ l →
    f c.1 c.2 = true → anyK f l = true := by
  intro l
  induction l with
  | nil => intro c hc; simp at hc
  | cons d l ih =>
    intro c hc h
    change (Bool.rec (anyK f l) true (f d.1 d.2) : Bool) = true
    rcases List.mem_cons.mp hc with rfl | hc
    · rw [h]
    · cases f d.1 d.2
      · exact ih c hc h
      · rfl

set_option maxRecDepth 100000 in
theorem node_complete (c t : ℕ) (ht : t = hiM ∨ t = fullM) (hD : ∀ i < nP, (sp t).testBit i = true) :
    ∀ (k : ℕ) (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ) (h : ℕ) (tl : List ℕ) (e : ℕ), tight t av L → normal av L →
      L.length ≤ k → (h :: tl).Nodup → (∀ v, v ∈ h :: tl ↔ v ∈ av ∧ used t L v) → e + (tl.length + 1) = k + 1 →
      (∀ g ∈ L.head?, g.1 = h ∨ g.2.1 = h ∨ h ≤ g.2.2) → node c k e (h :: tl) = true := by
  intro k
  induction k with
  | zero =>
    intro L av h tl e hti _ hl hn hm _ _
    have hL : L = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
    subst hL
    have e1 := single_of hn ((hm t).mpr ⟨hti.1, rfl⟩) (fun v hv => ((hm v).mp hv).2)
    rw [e1]
    exact isGoal_single t ht
  | succ k ih =>
    intro L av h tl e hti hno hl hn hm he ho
    change (Bool.rec (Bool.rec false (anyK (node c k) (kids e (h :: tl))) (collOK c (h :: tl))) true
      (isGoal (h :: tl)) : Bool) = true
    cases hg : isGoal (h :: tl)
    · rw [coll_ok c t ht L av (h :: tl) hti.1 hm]
      change anyK (node c k) (kids e (h :: tl)) = true
      cases L with
      | nil =>
        have e1 := single_of hn ((hm t).mpr ⟨hti.1, rfl⟩) (fun v hv => ((hm v).mp hv).2)
        rw [e1, isGoal_single t ht] at hg
        exact absurd hg (by simp)
      | cons g L' =>
        obtain ⟨ka, kb, slack, ha, hb, hz, hkept⟩ := step_child t hD av g L' (h :: tl) e k hti
          (by simpa using hl) hn hm (by simp only [List.length_cons]; omega)
        obtain ⟨c, ⟨kept, rfl, hkn, hkm, hkl⟩, hc⟩ := kids_hit e h tl g.1 g.2.1 g.2.2 ka kb hn ha hb hti.1.2.2.1
          hti.1.2.2.2.1 (ho g (by simp)) hz slack (fun kept hk => (hkept kept hk).1)
        apply anyK_of_mem _ _ _ hc
        obtain ⟨_, hnd, hmem⟩ := hkept kept hkm
        apply ih L' (insert g.2.2 av) g.2.2 kept _ (tight_tail hti) hno.2 (by simpa using hl) (hnd hkn) hmem
        · simp only [List.length_cons] at hkl
          omega
        · intro g2 hg2
          have nn := hno.1 g2 hg2
          cases L' with
          | nil => simp at hg2
          | cons g2' L'' =>
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hg2
            subst hg2
            have r := hti.1.2.2.2.2
            by_cases c1 : g2'.1 = g.2.2
            · exact Or.inl c1
            · by_cases c2 : g2'.2.1 = g.2.2
              · exact Or.inr (Or.inl c2)
              · right; right
                apply Nat.le_of_not_lt
                intro lt
                exact nn ⟨(Finset.mem_insert.mp r.1).resolve_left c1, (Finset.mem_insert.mp r.2.1).resolve_left c2, lt⟩
    · rfl

set_option maxRecDepth 100000 in
theorem root_complete (c t : ℕ) (ht : t = hiM ∨ t = fullM) (hD : ∀ i < nP, (sp t).testBit i = true)
    (k : ℕ) (L : List (ℕ × ℕ × ℕ)) (av : Finset ℕ) (ws : List ℕ) (e : ℕ) (hti : tight t av L) (hno : normal av L)
    (hl : L.length ≤ k + 1) (hn : ws.Nodup) (hm : ∀ v, v ∈ ws ↔ v ∈ av ∧ used t L v)
    (he : e + ws.length = k + 2) : root c k e ws = true := by
  change (Bool.rec (anyK (node c k) (kidsRoot e ws)) true (isGoal ws) : Bool) = true
  cases hg : isGoal ws
  · change anyK (node c k) (kidsRoot e ws) = true
    cases L with
    | nil =>
      have e1 := single_of hn ((hm t).mpr ⟨hti.1, rfl⟩) (fun v hv => ((hm v).mp hv).2)
      rw [e1, isGoal_single t ht] at hg
      exact absurd hg (by simp)
    | cons g L' =>
      obtain ⟨ka, kb, slack, ha, hb, hz, hkept⟩ := step_child t hD av g L' ws e k hti
        (by simpa using hl) hn hm he
      obtain ⟨c, ⟨kept, rfl, hkn, hkm, hkl⟩, hc⟩ := kidsRoot_hit e ws g.1 g.2.1 g.2.2 ka kb hn ha hb hti.1.2.2.1
        hti.1.2.2.2.1 hz slack (fun kept hk => (hkept kept hk).1)
      apply anyK_of_mem _ _ _ hc
      obtain ⟨_, hnd, hmem⟩ := hkept kept hkm
      apply node_complete c t ht hD k L' (insert g.2.2 av) g.2.2 kept _ (tight_tail hti) hno.2 (by simpa using hl)
        (hnd hkn) hmem
      · omega
      · intro g2 hg2
        have nn := hno.1 g2 hg2
        cases L' with
        | nil => simp at hg2
        | cons g2' L'' =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hg2
          subst hg2
          have r := hti.1.2.2.2.2
          by_cases c1 : g2'.1 = g.2.2
          · exact Or.inl c1
          · by_cases c2 : g2'.2.1 = g.2.2
            · exact Or.inr (Or.inl c2)
            · right; right
              apply Nat.le_of_not_lt
              intro lt
              exact nn ⟨(Finset.mem_insert.mp r.1).resolve_left c1, (Finset.mem_insert.mp r.2.1).resolve_left c2, lt⟩
  · rfl

set_option maxRecDepth 100000 in
theorem searchN_complete (c t : ℕ) (ht : t = hiM ∨ t = fullM) (hD : ∀ i < nP, (sp t).testBit i = true)
    (k : ℕ) (inputs : List ℕ) (hn : inputs.Nodup) (L : List (ℕ × ℕ × ℕ)) (hr : run t inputs.toFinset L)
    (hl : L.length ≤ k + 1) : searchN c k inputs = true := by
  classical
  obtain ⟨L0, ht0, hl0⟩ := exists_tight hr
  obtain ⟨L1, l1, r1, n1⟩ := sort_normal t L0 _ ht0.1
  have ht1 : tight t inputs.toFinset L1 := ⟨r1, fun L' h' => l1 ▸ ht0.2 L' h'⟩
  let ws := inputs.filter (fun v => decide (used t L1 v))
  have hm : ∀ v, v ∈ ws ↔ v ∈ inputs.toFinset ∧ used t L1 v := by
    intro v; simp [ws]
  have hnd : ws.Nodup := hn.filter _
  have hc := frontier_card t L1 _ ws ht1 hnd (fun v hv => (hm v).mp hv)
  have hcut : cutFull ws = true := by
    have le : allM ≤ cutN ws ||| hiM := by
      apply ge_of_bits
      intro i hi
      rw [Nat.testBit_or, Bool.or_eq_true]
      by_cases c : i < nP
      · left
        obtain ⟨w, hw, hu, hb⟩ := run_sep t (fun w => (sp w).testBit i = true) (hD i c)
          (fun a b z hz h => ops_sep i a b z hz h) L1 _ r1
        exact (cutN_bit ws i).mpr ⟨w, (hm w).mpr ⟨hw, hu⟩, hb⟩
      · exact Or.inr (hiM_bit i (by omega) hi)
    have z0 : Nat.sub allM (Nat.lor (cutN ws) hiM) = 0 := Nat.sub_eq_zero_of_le le
    unfold cutFull
    rw [z0]
    rfl
  have hroot := root_complete c t ht hD k L1 _ ws (k + 2 - ws.length) ht1 n1 (by omega) hnd hm (by omega)
  unfold searchN
  exact List.any_eq_true.mpr ⟨ws, List.mem_sublists.mpr List.filter_sublist,
    by simp [hcut, hroot]; omega⟩

set_option maxRecDepth 100000 in
theorem anyK_append_false (f : ℕ → List ℕ → Bool) : ∀ l1 l2 : List (ℕ × List ℕ), anyK f l1 = false →
    anyK f l2 = false → anyK f (l1 ++ l2) = false := by
  intro l1
  induction l1 with
  | nil => intro l2 _ h2; exact h2
  | cons d l1 ih =>
    intro l2 h1 h2
    change (Bool.rec (anyK f l1) true (f d.1 d.2) : Bool) = false at h1
    change (Bool.rec (anyK f (l1 ++ l2)) true (f d.1 d.2) : Bool) = false
    cases hd : f d.1 d.2
    · rw [hd] at h1
      exact ih l2 h1 h2
    · rw [hd] at h1
      exact absurd h1 (by simp)

set_option maxRecDepth 100000 in
theorem chainK (f : ℕ → List ℕ → Bool) (l : List (ℕ × List ℕ)) (i d j : ℕ) (hj : i + d = j)
    (h1 : anyK f ((l.drop i).take d) = false) (h2 : anyK f (l.drop j) = false) : anyK f (l.drop i) = false := by
  subst hj
  have h := anyK_append_false f ((l.drop i).take d) ((l.drop i).drop d) h1 (by rw [List.drop_drop]; exact h2)
  rwa [List.take_append_drop] at h

set_option maxRecDepth 100000 in
theorem startK (f : ℕ → List ℕ → Bool) (l : List (ℕ × List ℕ)) (h : anyK f (l.drop 0) = false) :
    anyK f l = false := by
  simpa using h

set_option maxRecDepth 100000 in
theorem takeOneK (f : ℕ → List ℕ → Bool) (l : List (ℕ × List ℕ)) (h : f (hdK l).1 (hdK l).2 = false) :
    anyK f (l.take 1) = false := by
  cases l with
  | nil => rfl
  | cons c l =>
    change f c.1 c.2 = false at h
    change (Bool.rec false true (f c.1 c.2) : Bool) = false
    rw [h]

set_option maxRecDepth 100000 in
theorem node_split (c k e : ℕ) (ws : List ℕ) (hg : isGoal ws = false) (h : anyK (node c k) (kids e ws) = false) :
    node c (k + 1) e ws = false := by
  change (Bool.rec (Bool.rec false (anyK (node c k) (kids e ws)) (collOK c ws)) true (isGoal ws) : Bool) = false
  rw [hg, h]
  cases collOK c ws <;> rfl

set_option maxRecDepth 100000 in
theorem root_split (c k e : ℕ) (ws : List ℕ) (hg : isGoal ws = false) (h : anyK (node c k) (kidsRoot e ws) = false) :
    root c k e ws = false := by
  change (Bool.rec (anyK (node c k) (kidsRoot e ws)) true (isGoal ws) : Bool) = false
  rw [hg]
  exact h

set_option maxRecDepth 100000 in
theorem toNat_ops (a b z : W) (hz : z ∈ ops a b) : z.toNat ∈ opsN a.toNat b.toNat := by
  have e : ∀ x y : W, x &&& ~~~y = x ^^^ (x &&& y) := by
    intro x y
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_xor, hi, decide_true, Bool.true_and]
    cases x.getLsbD i <;> cases y.getLsbD i <;> rfl
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hz
  simp only [opsN, List.mem_cons, List.not_mem_nil, or_false]
  rcases hz with rfl | rfl | rfl | rfl
  · exact Or.inl (BitVec.toNat_and a b)
  · exact Or.inr (Or.inl (BitVec.toNat_or a b))
  · right; right; left
    rw [e, BitVec.toNat_xor, BitVec.toNat_and]; rfl
  · right; right; right
    rw [e, BitVec.toNat_xor, BitVec.toNat_and, Nat.and_comm]; rfl

set_option maxRecDepth 100000 in
theorem run_of_build (t : W) : ∀ (k : ℕ) (av : Finset W), build basicOps t k av →
    ∃ L : List (ℕ × ℕ × ℕ), L.length ≤ k ∧ run t.toNat (av.image BitVec.toNat) L := by
  intro k
  induction k with
  | zero => intro av h; exact ⟨[], Nat.le_refl _, Finset.mem_image_of_mem _ h⟩
  | succ k ih =>
    intro av h
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨L, hl, hr⟩ := ih av skip
      exact ⟨L, by omega, hr⟩
    · obtain ⟨L, hl, hr⟩ := ih _ tail
      rw [Finset.image_insert] at hr
      exact ⟨(a.toNat, b.toNat, z.toNat) :: L, by simp only [List.length_cons]; omega,
        Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb, fun e => hab (BitVec.eq_of_toNat_eq e),
        toNat_ops a b z (List.mem_toFinset.mp hz), hr⟩

set_option maxRecDepth 100000 in
theorem low_bits (x : ℕ) (h : Nat.land x fullM = fullM) : ∀ i < nP, x.testBit i = true := by
  intro i hi
  have e := congrArg (fun y => Nat.testBit y i) h
  change (x &&& (2 ^ nP - 1)).testBit i = (2 ^ nP - 1).testBit i at e
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one] at e
  simpa [hi] using e

end Fast

def F (x : Fin 6 → Bool) : Bool := Nat.testBit (4276808426 * 2 ^ 32 + 4272482440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

set_option maxRecDepth 100000 in
theorem bound_from_searchN (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : searchN 1 8 (inputs.map BitVec.toNat) = false)
    (g1 : goal.toNat = hiM) (g2 : (~~~goal).toNat = fullM)
    (d1 : Nat.land (sp hiM) fullM = fullM) (d2 : Nat.land (sp fullM) fullM = fullM)
    (sample : ∀ k : Fin 256, F (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    9 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 256) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run0⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t c inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  obtain ⟨L, hl, hr⟩ := run_of_build t 9 _ (lift low run0)
  have himg : inputs.toFinset.image BitVec.toNat = (inputs.map BitVec.toNat).toFinset := by
    ext v; simp
  rw [himg] at hr
  have ht' : t.toNat = hiM ∨ t.toNat = fullM := by
    rcases ht with rfl | rfl
    · exact Or.inl g1
    · exact Or.inr g2
  have hD : ∀ i < nP, (sp t.toNat).testBit i = true := by
    rcases ht' with e | e <;> rw [e]
    · exact low_bits _ d1
    · exact low_bits _ d2
  have fin := searchN_complete 1 t.toNat ht' hD 8 (inputs.map BitVec.toNat)
    ((List.nodup_map_iff (fun _ _ h => BitVec.eq_of_toNat_eq h)).mpr nd) L hr hl
  exact Bool.noConfusion (reject.symm.trans fin)

def r0 : W := (0x0800030521411a22#64 ++ 0x80000410900cd0d5#64 ++ 0xee96ef4ff1e7ffb2#64 ++ 0xb2023cf1f01ff1ff#64 : BitVec 256)
def r1 : W := (0x13cdd488da802088#64 ++ 0x000cd1464862262a#64 ++ 0x5bcd95b9ded829ec#64 ++ 0x5e1dd34e48e23e3f#64 : BitVec 256)
def r2 : W := (0x442300da273a2658#64 ++ 0x4461628b8b034b4c#64 ++ 0x44229af20fba2a79#64 ++ 0xc5e1e38f8f03cfcc#64 : BitVec 256)
def r3 : W := (0x3010744650688d45#64 ++ 0x0ab603f005b40db0#64 ++ 0x136970574d2cfd1f#64 ++ 0x0bfe03f00ffc0ff0#64 : BitVec 256)
def r4 : W := (0x2bc1aa198a050008#64 ++ 0x7bdbfc000edbb000#64 ++ 0x3b6faa9f4806828f#64 ++ 0x7ffffc000ffff000#64 : BitVec 256)
def r5 : W := (0x6058e430842e44d5#64 ++ 0x1fffbbed60000000#64 ++ 0xfd18d7f4a71756dd#64 ++ 0xf7fffffff0000000#64 : BitVec 256)
def rows : List W := [r0, r1, r2, r3, r4, r5]
def n0 : ℕ := (((0x0800030521411a22 * 2 ^ 64 + 0x80000410900cd0d5) * 2 ^ 64 + 0xee96ef4ff1e7ffb2) * 2 ^ 64 + 0xb2023cf1f01ff1ff)
def n1 : ℕ := (((0x13cdd488da802088 * 2 ^ 64 + 0x000cd1464862262a) * 2 ^ 64 + 0x5bcd95b9ded829ec) * 2 ^ 64 + 0x5e1dd34e48e23e3f)
def n2 : ℕ := (((0x442300da273a2658 * 2 ^ 64 + 0x4461628b8b034b4c) * 2 ^ 64 + 0x44229af20fba2a79) * 2 ^ 64 + 0xc5e1e38f8f03cfcc)
def n3 : ℕ := (((0x3010744650688d45 * 2 ^ 64 + 0x0ab603f005b40db0) * 2 ^ 64 + 0x136970574d2cfd1f) * 2 ^ 64 + 0x0bfe03f00ffc0ff0)
def n4 : ℕ := (((0x2bc1aa198a050008 * 2 ^ 64 + 0x7bdbfc000edbb000) * 2 ^ 64 + 0x3b6faa9f4806828f) * 2 ^ 64 + 0x7ffffc000ffff000)
def n5 : ℕ := (((0x6058e430842e44d5 * 2 ^ 64 + 0x1fffbbed60000000) * 2 ^ 64 + 0xfd18d7f4a71756dd) * 2 ^ 64 + 0xf7fffffff0000000)
def rowsN : List ℕ := [n0, n1, n2, n3, n4, n5]

theorem rows_eq : rows.map BitVec.toNat = rowsN := by
  decide +kernel

theorem only_full : ∀ ws ∈ rowsN.sublists, (decide (ws.length ≤ 8 + 2) && cutFull ws) = true → ws = rowsN := by
  decide +kernel

def kR : List (ℕ × List ℕ) := kidsRoot 4 rowsN

set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem qr_60 : anyK (node 1 8) (List.drop 60 kR) = false := by decide +kernel
def k59 := kids (hdK (kR.drop 59)).1 (hdK (kR.drop 59)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail59_65 : anyK (node 1 7) (k59.drop 65) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part59_64 : anyK (node 1 7) ((k59.drop 64).take 1) = false := by decide +kernel
theorem tail59_64 : anyK (node 1 7) (k59.drop 64) = false := chainK _ _ 64 1 65 rfl part59_64 tail59_65
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part59_56 : anyK (node 1 7) ((k59.drop 56).take 8) = false := by decide +kernel
theorem tail59_56 : anyK (node 1 7) (k59.drop 56) = false := chainK _ _ 56 8 64 rfl part59_56 tail59_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part59_48 : anyK (node 1 7) ((k59.drop 48).take 8) = false := by decide +kernel
theorem tail59_48 : anyK (node 1 7) (k59.drop 48) = false := chainK _ _ 48 8 56 rfl part59_48 tail59_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part59_40 : anyK (node 1 7) ((k59.drop 40).take 8) = false := by decide +kernel
theorem tail59_40 : anyK (node 1 7) (k59.drop 40) = false := chainK _ _ 40 8 48 rfl part59_40 tail59_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part59_32 : anyK (node 1 7) ((k59.drop 32).take 8) = false := by decide +kernel
theorem tail59_32 : anyK (node 1 7) (k59.drop 32) = false := chainK _ _ 32 8 40 rfl part59_32 tail59_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part59_24 : anyK (node 1 7) ((k59.drop 24).take 8) = false := by decide +kernel
theorem tail59_24 : anyK (node 1 7) (k59.drop 24) = false := chainK _ _ 24 8 32 rfl part59_24 tail59_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part59_16 : anyK (node 1 7) ((k59.drop 16).take 8) = false := by decide +kernel
theorem tail59_16 : anyK (node 1 7) (k59.drop 16) = false := chainK _ _ 16 8 24 rfl part59_16 tail59_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part59_8 : anyK (node 1 7) ((k59.drop 8).take 8) = false := by decide +kernel
theorem tail59_8 : anyK (node 1 7) (k59.drop 8) = false := chainK _ _ 8 8 16 rfl part59_8 tail59_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part59_0 : anyK (node 1 7) ((k59.drop 0).take 8) = false := by decide +kernel
theorem tail59_0 : anyK (node 1 7) (k59.drop 0) = false := chainK _ _ 0 8 8 rfl part59_0 tail59_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_59 : anyK (node 1 8) ((kR.drop 59).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k59 tail59_0))
theorem qr_59 : anyK (node 1 8) (List.drop 59 kR) = false :=
  chainK (node 1 8) kR 59 1 60 rfl cr_59 qr_60
def k58 := kids (hdK (kR.drop 58)).1 (hdK (kR.drop 58)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail58_92 : anyK (node 1 7) (k58.drop 92) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part58_88 : anyK (node 1 7) ((k58.drop 88).take 4) = false := by decide +kernel
theorem tail58_88 : anyK (node 1 7) (k58.drop 88) = false := chainK _ _ 88 4 92 rfl part58_88 tail58_92
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part58_80 : anyK (node 1 7) ((k58.drop 80).take 8) = false := by decide +kernel
theorem tail58_80 : anyK (node 1 7) (k58.drop 80) = false := chainK _ _ 80 8 88 rfl part58_80 tail58_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part58_72 : anyK (node 1 7) ((k58.drop 72).take 8) = false := by decide +kernel
theorem tail58_72 : anyK (node 1 7) (k58.drop 72) = false := chainK _ _ 72 8 80 rfl part58_72 tail58_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part58_64 : anyK (node 1 7) ((k58.drop 64).take 8) = false := by decide +kernel
theorem tail58_64 : anyK (node 1 7) (k58.drop 64) = false := chainK _ _ 64 8 72 rfl part58_64 tail58_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part58_56 : anyK (node 1 7) ((k58.drop 56).take 8) = false := by decide +kernel
theorem tail58_56 : anyK (node 1 7) (k58.drop 56) = false := chainK _ _ 56 8 64 rfl part58_56 tail58_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part58_48 : anyK (node 1 7) ((k58.drop 48).take 8) = false := by decide +kernel
theorem tail58_48 : anyK (node 1 7) (k58.drop 48) = false := chainK _ _ 48 8 56 rfl part58_48 tail58_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part58_40 : anyK (node 1 7) ((k58.drop 40).take 8) = false := by decide +kernel
theorem tail58_40 : anyK (node 1 7) (k58.drop 40) = false := chainK _ _ 40 8 48 rfl part58_40 tail58_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part58_32 : anyK (node 1 7) ((k58.drop 32).take 8) = false := by decide +kernel
theorem tail58_32 : anyK (node 1 7) (k58.drop 32) = false := chainK _ _ 32 8 40 rfl part58_32 tail58_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part58_24 : anyK (node 1 7) ((k58.drop 24).take 8) = false := by decide +kernel
theorem tail58_24 : anyK (node 1 7) (k58.drop 24) = false := chainK _ _ 24 8 32 rfl part58_24 tail58_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part58_16 : anyK (node 1 7) ((k58.drop 16).take 8) = false := by decide +kernel
theorem tail58_16 : anyK (node 1 7) (k58.drop 16) = false := chainK _ _ 16 8 24 rfl part58_16 tail58_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part58_8 : anyK (node 1 7) ((k58.drop 8).take 8) = false := by decide +kernel
theorem tail58_8 : anyK (node 1 7) (k58.drop 8) = false := chainK _ _ 8 8 16 rfl part58_8 tail58_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part58_0 : anyK (node 1 7) ((k58.drop 0).take 8) = false := by decide +kernel
theorem tail58_0 : anyK (node 1 7) (k58.drop 0) = false := chainK _ _ 0 8 8 rfl part58_0 tail58_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_58 : anyK (node 1 8) ((kR.drop 58).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k58 tail58_0))
theorem qr_58 : anyK (node 1 8) (List.drop 58 kR) = false :=
  chainK (node 1 8) kR 58 1 59 rfl cr_58 qr_59
def k57 := kids (hdK (kR.drop 57)).1 (hdK (kR.drop 57)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail57_47 : anyK (node 1 7) (k57.drop 47) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part57_40 : anyK (node 1 7) ((k57.drop 40).take 7) = false := by decide +kernel
theorem tail57_40 : anyK (node 1 7) (k57.drop 40) = false := chainK _ _ 40 7 47 rfl part57_40 tail57_47
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part57_32 : anyK (node 1 7) ((k57.drop 32).take 8) = false := by decide +kernel
theorem tail57_32 : anyK (node 1 7) (k57.drop 32) = false := chainK _ _ 32 8 40 rfl part57_32 tail57_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part57_24 : anyK (node 1 7) ((k57.drop 24).take 8) = false := by decide +kernel
theorem tail57_24 : anyK (node 1 7) (k57.drop 24) = false := chainK _ _ 24 8 32 rfl part57_24 tail57_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part57_16 : anyK (node 1 7) ((k57.drop 16).take 8) = false := by decide +kernel
theorem tail57_16 : anyK (node 1 7) (k57.drop 16) = false := chainK _ _ 16 8 24 rfl part57_16 tail57_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part57_8 : anyK (node 1 7) ((k57.drop 8).take 8) = false := by decide +kernel
theorem tail57_8 : anyK (node 1 7) (k57.drop 8) = false := chainK _ _ 8 8 16 rfl part57_8 tail57_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part57_0 : anyK (node 1 7) ((k57.drop 0).take 8) = false := by decide +kernel
theorem tail57_0 : anyK (node 1 7) (k57.drop 0) = false := chainK _ _ 0 8 8 rfl part57_0 tail57_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_57 : anyK (node 1 8) ((kR.drop 57).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k57 tail57_0))
theorem qr_57 : anyK (node 1 8) (List.drop 57 kR) = false :=
  chainK (node 1 8) kR 57 1 58 rfl cr_57 qr_58
def k56 := kids (hdK (kR.drop 56)).1 (hdK (kR.drop 56)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail56_74 : anyK (node 1 7) (k56.drop 74) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part56_72 : anyK (node 1 7) ((k56.drop 72).take 2) = false := by decide +kernel
theorem tail56_72 : anyK (node 1 7) (k56.drop 72) = false := chainK _ _ 72 2 74 rfl part56_72 tail56_74
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part56_64 : anyK (node 1 7) ((k56.drop 64).take 8) = false := by decide +kernel
theorem tail56_64 : anyK (node 1 7) (k56.drop 64) = false := chainK _ _ 64 8 72 rfl part56_64 tail56_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part56_56 : anyK (node 1 7) ((k56.drop 56).take 8) = false := by decide +kernel
theorem tail56_56 : anyK (node 1 7) (k56.drop 56) = false := chainK _ _ 56 8 64 rfl part56_56 tail56_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part56_48 : anyK (node 1 7) ((k56.drop 48).take 8) = false := by decide +kernel
theorem tail56_48 : anyK (node 1 7) (k56.drop 48) = false := chainK _ _ 48 8 56 rfl part56_48 tail56_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part56_40 : anyK (node 1 7) ((k56.drop 40).take 8) = false := by decide +kernel
theorem tail56_40 : anyK (node 1 7) (k56.drop 40) = false := chainK _ _ 40 8 48 rfl part56_40 tail56_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part56_32 : anyK (node 1 7) ((k56.drop 32).take 8) = false := by decide +kernel
theorem tail56_32 : anyK (node 1 7) (k56.drop 32) = false := chainK _ _ 32 8 40 rfl part56_32 tail56_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part56_24 : anyK (node 1 7) ((k56.drop 24).take 8) = false := by decide +kernel
theorem tail56_24 : anyK (node 1 7) (k56.drop 24) = false := chainK _ _ 24 8 32 rfl part56_24 tail56_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part56_16 : anyK (node 1 7) ((k56.drop 16).take 8) = false := by decide +kernel
theorem tail56_16 : anyK (node 1 7) (k56.drop 16) = false := chainK _ _ 16 8 24 rfl part56_16 tail56_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part56_8 : anyK (node 1 7) ((k56.drop 8).take 8) = false := by decide +kernel
theorem tail56_8 : anyK (node 1 7) (k56.drop 8) = false := chainK _ _ 8 8 16 rfl part56_8 tail56_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part56_0 : anyK (node 1 7) ((k56.drop 0).take 8) = false := by decide +kernel
theorem tail56_0 : anyK (node 1 7) (k56.drop 0) = false := chainK _ _ 0 8 8 rfl part56_0 tail56_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_56 : anyK (node 1 8) ((kR.drop 56).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k56 tail56_0))
theorem qr_56 : anyK (node 1 8) (List.drop 56 kR) = false :=
  chainK (node 1 8) kR 56 1 57 rfl cr_56 qr_57
def k55 := kids (hdK (kR.drop 55)).1 (hdK (kR.drop 55)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail55_66 : anyK (node 1 7) (k55.drop 66) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part55_64 : anyK (node 1 7) ((k55.drop 64).take 2) = false := by decide +kernel
theorem tail55_64 : anyK (node 1 7) (k55.drop 64) = false := chainK _ _ 64 2 66 rfl part55_64 tail55_66
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part55_56 : anyK (node 1 7) ((k55.drop 56).take 8) = false := by decide +kernel
theorem tail55_56 : anyK (node 1 7) (k55.drop 56) = false := chainK _ _ 56 8 64 rfl part55_56 tail55_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part55_48 : anyK (node 1 7) ((k55.drop 48).take 8) = false := by decide +kernel
theorem tail55_48 : anyK (node 1 7) (k55.drop 48) = false := chainK _ _ 48 8 56 rfl part55_48 tail55_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part55_40 : anyK (node 1 7) ((k55.drop 40).take 8) = false := by decide +kernel
theorem tail55_40 : anyK (node 1 7) (k55.drop 40) = false := chainK _ _ 40 8 48 rfl part55_40 tail55_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part55_32 : anyK (node 1 7) ((k55.drop 32).take 8) = false := by decide +kernel
theorem tail55_32 : anyK (node 1 7) (k55.drop 32) = false := chainK _ _ 32 8 40 rfl part55_32 tail55_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part55_24 : anyK (node 1 7) ((k55.drop 24).take 8) = false := by decide +kernel
theorem tail55_24 : anyK (node 1 7) (k55.drop 24) = false := chainK _ _ 24 8 32 rfl part55_24 tail55_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part55_16 : anyK (node 1 7) ((k55.drop 16).take 8) = false := by decide +kernel
theorem tail55_16 : anyK (node 1 7) (k55.drop 16) = false := chainK _ _ 16 8 24 rfl part55_16 tail55_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part55_8 : anyK (node 1 7) ((k55.drop 8).take 8) = false := by decide +kernel
theorem tail55_8 : anyK (node 1 7) (k55.drop 8) = false := chainK _ _ 8 8 16 rfl part55_8 tail55_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part55_0 : anyK (node 1 7) ((k55.drop 0).take 8) = false := by decide +kernel
theorem tail55_0 : anyK (node 1 7) (k55.drop 0) = false := chainK _ _ 0 8 8 rfl part55_0 tail55_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_55 : anyK (node 1 8) ((kR.drop 55).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k55 tail55_0))
theorem qr_55 : anyK (node 1 8) (List.drop 55 kR) = false :=
  chainK (node 1 8) kR 55 1 56 rfl cr_55 qr_56
def k54 := kids (hdK (kR.drop 54)).1 (hdK (kR.drop 54)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail54_89 : anyK (node 1 7) (k54.drop 89) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part54_88 : anyK (node 1 7) ((k54.drop 88).take 1) = false := by decide +kernel
theorem tail54_88 : anyK (node 1 7) (k54.drop 88) = false := chainK _ _ 88 1 89 rfl part54_88 tail54_89
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part54_80 : anyK (node 1 7) ((k54.drop 80).take 8) = false := by decide +kernel
theorem tail54_80 : anyK (node 1 7) (k54.drop 80) = false := chainK _ _ 80 8 88 rfl part54_80 tail54_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part54_72 : anyK (node 1 7) ((k54.drop 72).take 8) = false := by decide +kernel
theorem tail54_72 : anyK (node 1 7) (k54.drop 72) = false := chainK _ _ 72 8 80 rfl part54_72 tail54_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part54_64 : anyK (node 1 7) ((k54.drop 64).take 8) = false := by decide +kernel
theorem tail54_64 : anyK (node 1 7) (k54.drop 64) = false := chainK _ _ 64 8 72 rfl part54_64 tail54_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part54_56 : anyK (node 1 7) ((k54.drop 56).take 8) = false := by decide +kernel
theorem tail54_56 : anyK (node 1 7) (k54.drop 56) = false := chainK _ _ 56 8 64 rfl part54_56 tail54_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part54_48 : anyK (node 1 7) ((k54.drop 48).take 8) = false := by decide +kernel
theorem tail54_48 : anyK (node 1 7) (k54.drop 48) = false := chainK _ _ 48 8 56 rfl part54_48 tail54_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part54_40 : anyK (node 1 7) ((k54.drop 40).take 8) = false := by decide +kernel
theorem tail54_40 : anyK (node 1 7) (k54.drop 40) = false := chainK _ _ 40 8 48 rfl part54_40 tail54_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part54_32 : anyK (node 1 7) ((k54.drop 32).take 8) = false := by decide +kernel
theorem tail54_32 : anyK (node 1 7) (k54.drop 32) = false := chainK _ _ 32 8 40 rfl part54_32 tail54_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part54_24 : anyK (node 1 7) ((k54.drop 24).take 8) = false := by decide +kernel
theorem tail54_24 : anyK (node 1 7) (k54.drop 24) = false := chainK _ _ 24 8 32 rfl part54_24 tail54_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part54_16 : anyK (node 1 7) ((k54.drop 16).take 8) = false := by decide +kernel
theorem tail54_16 : anyK (node 1 7) (k54.drop 16) = false := chainK _ _ 16 8 24 rfl part54_16 tail54_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part54_8 : anyK (node 1 7) ((k54.drop 8).take 8) = false := by decide +kernel
theorem tail54_8 : anyK (node 1 7) (k54.drop 8) = false := chainK _ _ 8 8 16 rfl part54_8 tail54_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part54_0 : anyK (node 1 7) ((k54.drop 0).take 8) = false := by decide +kernel
theorem tail54_0 : anyK (node 1 7) (k54.drop 0) = false := chainK _ _ 0 8 8 rfl part54_0 tail54_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_54 : anyK (node 1 8) ((kR.drop 54).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k54 tail54_0))
theorem qr_54 : anyK (node 1 8) (List.drop 54 kR) = false :=
  chainK (node 1 8) kR 54 1 55 rfl cr_54 qr_55
def k53 := kids (hdK (kR.drop 53)).1 (hdK (kR.drop 53)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail53_45 : anyK (node 1 7) (k53.drop 45) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part53_40 : anyK (node 1 7) ((k53.drop 40).take 5) = false := by decide +kernel
theorem tail53_40 : anyK (node 1 7) (k53.drop 40) = false := chainK _ _ 40 5 45 rfl part53_40 tail53_45
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part53_32 : anyK (node 1 7) ((k53.drop 32).take 8) = false := by decide +kernel
theorem tail53_32 : anyK (node 1 7) (k53.drop 32) = false := chainK _ _ 32 8 40 rfl part53_32 tail53_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part53_24 : anyK (node 1 7) ((k53.drop 24).take 8) = false := by decide +kernel
theorem tail53_24 : anyK (node 1 7) (k53.drop 24) = false := chainK _ _ 24 8 32 rfl part53_24 tail53_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part53_16 : anyK (node 1 7) ((k53.drop 16).take 8) = false := by decide +kernel
theorem tail53_16 : anyK (node 1 7) (k53.drop 16) = false := chainK _ _ 16 8 24 rfl part53_16 tail53_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part53_8 : anyK (node 1 7) ((k53.drop 8).take 8) = false := by decide +kernel
theorem tail53_8 : anyK (node 1 7) (k53.drop 8) = false := chainK _ _ 8 8 16 rfl part53_8 tail53_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part53_0 : anyK (node 1 7) ((k53.drop 0).take 8) = false := by decide +kernel
theorem tail53_0 : anyK (node 1 7) (k53.drop 0) = false := chainK _ _ 0 8 8 rfl part53_0 tail53_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_53 : anyK (node 1 8) ((kR.drop 53).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k53 tail53_0))
theorem qr_53 : anyK (node 1 8) (List.drop 53 kR) = false :=
  chainK (node 1 8) kR 53 1 54 rfl cr_53 qr_54
def k52 := kids (hdK (kR.drop 52)).1 (hdK (kR.drop 52)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail52_75 : anyK (node 1 7) (k52.drop 75) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part52_72 : anyK (node 1 7) ((k52.drop 72).take 3) = false := by decide +kernel
theorem tail52_72 : anyK (node 1 7) (k52.drop 72) = false := chainK _ _ 72 3 75 rfl part52_72 tail52_75
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part52_64 : anyK (node 1 7) ((k52.drop 64).take 8) = false := by decide +kernel
theorem tail52_64 : anyK (node 1 7) (k52.drop 64) = false := chainK _ _ 64 8 72 rfl part52_64 tail52_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part52_56 : anyK (node 1 7) ((k52.drop 56).take 8) = false := by decide +kernel
theorem tail52_56 : anyK (node 1 7) (k52.drop 56) = false := chainK _ _ 56 8 64 rfl part52_56 tail52_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part52_48 : anyK (node 1 7) ((k52.drop 48).take 8) = false := by decide +kernel
theorem tail52_48 : anyK (node 1 7) (k52.drop 48) = false := chainK _ _ 48 8 56 rfl part52_48 tail52_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part52_40 : anyK (node 1 7) ((k52.drop 40).take 8) = false := by decide +kernel
theorem tail52_40 : anyK (node 1 7) (k52.drop 40) = false := chainK _ _ 40 8 48 rfl part52_40 tail52_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part52_32 : anyK (node 1 7) ((k52.drop 32).take 8) = false := by decide +kernel
theorem tail52_32 : anyK (node 1 7) (k52.drop 32) = false := chainK _ _ 32 8 40 rfl part52_32 tail52_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part52_24 : anyK (node 1 7) ((k52.drop 24).take 8) = false := by decide +kernel
theorem tail52_24 : anyK (node 1 7) (k52.drop 24) = false := chainK _ _ 24 8 32 rfl part52_24 tail52_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part52_16 : anyK (node 1 7) ((k52.drop 16).take 8) = false := by decide +kernel
theorem tail52_16 : anyK (node 1 7) (k52.drop 16) = false := chainK _ _ 16 8 24 rfl part52_16 tail52_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part52_8 : anyK (node 1 7) ((k52.drop 8).take 8) = false := by decide +kernel
theorem tail52_8 : anyK (node 1 7) (k52.drop 8) = false := chainK _ _ 8 8 16 rfl part52_8 tail52_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part52_0 : anyK (node 1 7) ((k52.drop 0).take 8) = false := by decide +kernel
theorem tail52_0 : anyK (node 1 7) (k52.drop 0) = false := chainK _ _ 0 8 8 rfl part52_0 tail52_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_52 : anyK (node 1 8) ((kR.drop 52).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k52 tail52_0))
theorem qr_52 : anyK (node 1 8) (List.drop 52 kR) = false :=
  chainK (node 1 8) kR 52 1 53 rfl cr_52 qr_53
def k51 := kids (hdK (kR.drop 51)).1 (hdK (kR.drop 51)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail51_90 : anyK (node 1 7) (k51.drop 90) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part51_88 : anyK (node 1 7) ((k51.drop 88).take 2) = false := by decide +kernel
theorem tail51_88 : anyK (node 1 7) (k51.drop 88) = false := chainK _ _ 88 2 90 rfl part51_88 tail51_90
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part51_80 : anyK (node 1 7) ((k51.drop 80).take 8) = false := by decide +kernel
theorem tail51_80 : anyK (node 1 7) (k51.drop 80) = false := chainK _ _ 80 8 88 rfl part51_80 tail51_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part51_72 : anyK (node 1 7) ((k51.drop 72).take 8) = false := by decide +kernel
theorem tail51_72 : anyK (node 1 7) (k51.drop 72) = false := chainK _ _ 72 8 80 rfl part51_72 tail51_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part51_64 : anyK (node 1 7) ((k51.drop 64).take 8) = false := by decide +kernel
theorem tail51_64 : anyK (node 1 7) (k51.drop 64) = false := chainK _ _ 64 8 72 rfl part51_64 tail51_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part51_56 : anyK (node 1 7) ((k51.drop 56).take 8) = false := by decide +kernel
theorem tail51_56 : anyK (node 1 7) (k51.drop 56) = false := chainK _ _ 56 8 64 rfl part51_56 tail51_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part51_48 : anyK (node 1 7) ((k51.drop 48).take 8) = false := by decide +kernel
theorem tail51_48 : anyK (node 1 7) (k51.drop 48) = false := chainK _ _ 48 8 56 rfl part51_48 tail51_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part51_40 : anyK (node 1 7) ((k51.drop 40).take 8) = false := by decide +kernel
theorem tail51_40 : anyK (node 1 7) (k51.drop 40) = false := chainK _ _ 40 8 48 rfl part51_40 tail51_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part51_32 : anyK (node 1 7) ((k51.drop 32).take 8) = false := by decide +kernel
theorem tail51_32 : anyK (node 1 7) (k51.drop 32) = false := chainK _ _ 32 8 40 rfl part51_32 tail51_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part51_24 : anyK (node 1 7) ((k51.drop 24).take 8) = false := by decide +kernel
theorem tail51_24 : anyK (node 1 7) (k51.drop 24) = false := chainK _ _ 24 8 32 rfl part51_24 tail51_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part51_16 : anyK (node 1 7) ((k51.drop 16).take 8) = false := by decide +kernel
theorem tail51_16 : anyK (node 1 7) (k51.drop 16) = false := chainK _ _ 16 8 24 rfl part51_16 tail51_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part51_8 : anyK (node 1 7) ((k51.drop 8).take 8) = false := by decide +kernel
theorem tail51_8 : anyK (node 1 7) (k51.drop 8) = false := chainK _ _ 8 8 16 rfl part51_8 tail51_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part51_0 : anyK (node 1 7) ((k51.drop 0).take 8) = false := by decide +kernel
theorem tail51_0 : anyK (node 1 7) (k51.drop 0) = false := chainK _ _ 0 8 8 rfl part51_0 tail51_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_51 : anyK (node 1 8) ((kR.drop 51).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k51 tail51_0))
theorem qr_51 : anyK (node 1 8) (List.drop 51 kR) = false :=
  chainK (node 1 8) kR 51 1 52 rfl cr_51 qr_52
def k50 := kids (hdK (kR.drop 50)).1 (hdK (kR.drop 50)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail50_85 : anyK (node 1 7) (k50.drop 85) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part50_80 : anyK (node 1 7) ((k50.drop 80).take 5) = false := by decide +kernel
theorem tail50_80 : anyK (node 1 7) (k50.drop 80) = false := chainK _ _ 80 5 85 rfl part50_80 tail50_85
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part50_72 : anyK (node 1 7) ((k50.drop 72).take 8) = false := by decide +kernel
theorem tail50_72 : anyK (node 1 7) (k50.drop 72) = false := chainK _ _ 72 8 80 rfl part50_72 tail50_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part50_64 : anyK (node 1 7) ((k50.drop 64).take 8) = false := by decide +kernel
theorem tail50_64 : anyK (node 1 7) (k50.drop 64) = false := chainK _ _ 64 8 72 rfl part50_64 tail50_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part50_56 : anyK (node 1 7) ((k50.drop 56).take 8) = false := by decide +kernel
theorem tail50_56 : anyK (node 1 7) (k50.drop 56) = false := chainK _ _ 56 8 64 rfl part50_56 tail50_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part50_48 : anyK (node 1 7) ((k50.drop 48).take 8) = false := by decide +kernel
theorem tail50_48 : anyK (node 1 7) (k50.drop 48) = false := chainK _ _ 48 8 56 rfl part50_48 tail50_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part50_40 : anyK (node 1 7) ((k50.drop 40).take 8) = false := by decide +kernel
theorem tail50_40 : anyK (node 1 7) (k50.drop 40) = false := chainK _ _ 40 8 48 rfl part50_40 tail50_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part50_32 : anyK (node 1 7) ((k50.drop 32).take 8) = false := by decide +kernel
theorem tail50_32 : anyK (node 1 7) (k50.drop 32) = false := chainK _ _ 32 8 40 rfl part50_32 tail50_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part50_24 : anyK (node 1 7) ((k50.drop 24).take 8) = false := by decide +kernel
theorem tail50_24 : anyK (node 1 7) (k50.drop 24) = false := chainK _ _ 24 8 32 rfl part50_24 tail50_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part50_16 : anyK (node 1 7) ((k50.drop 16).take 8) = false := by decide +kernel
theorem tail50_16 : anyK (node 1 7) (k50.drop 16) = false := chainK _ _ 16 8 24 rfl part50_16 tail50_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part50_8 : anyK (node 1 7) ((k50.drop 8).take 8) = false := by decide +kernel
theorem tail50_8 : anyK (node 1 7) (k50.drop 8) = false := chainK _ _ 8 8 16 rfl part50_8 tail50_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part50_0 : anyK (node 1 7) ((k50.drop 0).take 8) = false := by decide +kernel
theorem tail50_0 : anyK (node 1 7) (k50.drop 0) = false := chainK _ _ 0 8 8 rfl part50_0 tail50_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_50 : anyK (node 1 8) ((kR.drop 50).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k50 tail50_0))
theorem qr_50 : anyK (node 1 8) (List.drop 50 kR) = false :=
  chainK (node 1 8) kR 50 1 51 rfl cr_50 qr_51
def k49 := kids (hdK (kR.drop 49)).1 (hdK (kR.drop 49)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail49_60 : anyK (node 1 7) (k49.drop 60) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part49_56 : anyK (node 1 7) ((k49.drop 56).take 4) = false := by decide +kernel
theorem tail49_56 : anyK (node 1 7) (k49.drop 56) = false := chainK _ _ 56 4 60 rfl part49_56 tail49_60
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part49_48 : anyK (node 1 7) ((k49.drop 48).take 8) = false := by decide +kernel
theorem tail49_48 : anyK (node 1 7) (k49.drop 48) = false := chainK _ _ 48 8 56 rfl part49_48 tail49_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part49_40 : anyK (node 1 7) ((k49.drop 40).take 8) = false := by decide +kernel
theorem tail49_40 : anyK (node 1 7) (k49.drop 40) = false := chainK _ _ 40 8 48 rfl part49_40 tail49_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part49_32 : anyK (node 1 7) ((k49.drop 32).take 8) = false := by decide +kernel
theorem tail49_32 : anyK (node 1 7) (k49.drop 32) = false := chainK _ _ 32 8 40 rfl part49_32 tail49_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part49_24 : anyK (node 1 7) ((k49.drop 24).take 8) = false := by decide +kernel
theorem tail49_24 : anyK (node 1 7) (k49.drop 24) = false := chainK _ _ 24 8 32 rfl part49_24 tail49_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part49_16 : anyK (node 1 7) ((k49.drop 16).take 8) = false := by decide +kernel
theorem tail49_16 : anyK (node 1 7) (k49.drop 16) = false := chainK _ _ 16 8 24 rfl part49_16 tail49_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part49_8 : anyK (node 1 7) ((k49.drop 8).take 8) = false := by decide +kernel
theorem tail49_8 : anyK (node 1 7) (k49.drop 8) = false := chainK _ _ 8 8 16 rfl part49_8 tail49_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part49_0 : anyK (node 1 7) ((k49.drop 0).take 8) = false := by decide +kernel
theorem tail49_0 : anyK (node 1 7) (k49.drop 0) = false := chainK _ _ 0 8 8 rfl part49_0 tail49_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_49 : anyK (node 1 8) ((kR.drop 49).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k49 tail49_0))
theorem qr_49 : anyK (node 1 8) (List.drop 49 kR) = false :=
  chainK (node 1 8) kR 49 1 50 rfl cr_49 qr_50
def k48 := kids (hdK (kR.drop 48)).1 (hdK (kR.drop 48)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail48_87 : anyK (node 1 7) (k48.drop 87) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part48_80 : anyK (node 1 7) ((k48.drop 80).take 7) = false := by decide +kernel
theorem tail48_80 : anyK (node 1 7) (k48.drop 80) = false := chainK _ _ 80 7 87 rfl part48_80 tail48_87
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part48_72 : anyK (node 1 7) ((k48.drop 72).take 8) = false := by decide +kernel
theorem tail48_72 : anyK (node 1 7) (k48.drop 72) = false := chainK _ _ 72 8 80 rfl part48_72 tail48_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part48_64 : anyK (node 1 7) ((k48.drop 64).take 8) = false := by decide +kernel
theorem tail48_64 : anyK (node 1 7) (k48.drop 64) = false := chainK _ _ 64 8 72 rfl part48_64 tail48_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part48_56 : anyK (node 1 7) ((k48.drop 56).take 8) = false := by decide +kernel
theorem tail48_56 : anyK (node 1 7) (k48.drop 56) = false := chainK _ _ 56 8 64 rfl part48_56 tail48_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part48_48 : anyK (node 1 7) ((k48.drop 48).take 8) = false := by decide +kernel
theorem tail48_48 : anyK (node 1 7) (k48.drop 48) = false := chainK _ _ 48 8 56 rfl part48_48 tail48_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part48_40 : anyK (node 1 7) ((k48.drop 40).take 8) = false := by decide +kernel
theorem tail48_40 : anyK (node 1 7) (k48.drop 40) = false := chainK _ _ 40 8 48 rfl part48_40 tail48_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part48_32 : anyK (node 1 7) ((k48.drop 32).take 8) = false := by decide +kernel
theorem tail48_32 : anyK (node 1 7) (k48.drop 32) = false := chainK _ _ 32 8 40 rfl part48_32 tail48_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part48_24 : anyK (node 1 7) ((k48.drop 24).take 8) = false := by decide +kernel
theorem tail48_24 : anyK (node 1 7) (k48.drop 24) = false := chainK _ _ 24 8 32 rfl part48_24 tail48_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part48_16 : anyK (node 1 7) ((k48.drop 16).take 8) = false := by decide +kernel
theorem tail48_16 : anyK (node 1 7) (k48.drop 16) = false := chainK _ _ 16 8 24 rfl part48_16 tail48_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part48_8 : anyK (node 1 7) ((k48.drop 8).take 8) = false := by decide +kernel
theorem tail48_8 : anyK (node 1 7) (k48.drop 8) = false := chainK _ _ 8 8 16 rfl part48_8 tail48_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part48_0 : anyK (node 1 7) ((k48.drop 0).take 8) = false := by decide +kernel
theorem tail48_0 : anyK (node 1 7) (k48.drop 0) = false := chainK _ _ 0 8 8 rfl part48_0 tail48_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_48 : anyK (node 1 8) ((kR.drop 48).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k48 tail48_0))
theorem qr_48 : anyK (node 1 8) (List.drop 48 kR) = false :=
  chainK (node 1 8) kR 48 1 49 rfl cr_48 qr_49
def k47 := kids (hdK (kR.drop 47)).1 (hdK (kR.drop 47)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail47_74 : anyK (node 1 7) (k47.drop 74) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part47_72 : anyK (node 1 7) ((k47.drop 72).take 2) = false := by decide +kernel
theorem tail47_72 : anyK (node 1 7) (k47.drop 72) = false := chainK _ _ 72 2 74 rfl part47_72 tail47_74
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part47_64 : anyK (node 1 7) ((k47.drop 64).take 8) = false := by decide +kernel
theorem tail47_64 : anyK (node 1 7) (k47.drop 64) = false := chainK _ _ 64 8 72 rfl part47_64 tail47_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part47_56 : anyK (node 1 7) ((k47.drop 56).take 8) = false := by decide +kernel
theorem tail47_56 : anyK (node 1 7) (k47.drop 56) = false := chainK _ _ 56 8 64 rfl part47_56 tail47_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part47_48 : anyK (node 1 7) ((k47.drop 48).take 8) = false := by decide +kernel
theorem tail47_48 : anyK (node 1 7) (k47.drop 48) = false := chainK _ _ 48 8 56 rfl part47_48 tail47_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part47_40 : anyK (node 1 7) ((k47.drop 40).take 8) = false := by decide +kernel
theorem tail47_40 : anyK (node 1 7) (k47.drop 40) = false := chainK _ _ 40 8 48 rfl part47_40 tail47_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part47_32 : anyK (node 1 7) ((k47.drop 32).take 8) = false := by decide +kernel
theorem tail47_32 : anyK (node 1 7) (k47.drop 32) = false := chainK _ _ 32 8 40 rfl part47_32 tail47_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part47_24 : anyK (node 1 7) ((k47.drop 24).take 8) = false := by decide +kernel
theorem tail47_24 : anyK (node 1 7) (k47.drop 24) = false := chainK _ _ 24 8 32 rfl part47_24 tail47_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part47_16 : anyK (node 1 7) ((k47.drop 16).take 8) = false := by decide +kernel
theorem tail47_16 : anyK (node 1 7) (k47.drop 16) = false := chainK _ _ 16 8 24 rfl part47_16 tail47_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part47_8 : anyK (node 1 7) ((k47.drop 8).take 8) = false := by decide +kernel
theorem tail47_8 : anyK (node 1 7) (k47.drop 8) = false := chainK _ _ 8 8 16 rfl part47_8 tail47_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part47_0 : anyK (node 1 7) ((k47.drop 0).take 8) = false := by decide +kernel
theorem tail47_0 : anyK (node 1 7) (k47.drop 0) = false := chainK _ _ 0 8 8 rfl part47_0 tail47_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_47 : anyK (node 1 8) ((kR.drop 47).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k47 tail47_0))
theorem qr_47 : anyK (node 1 8) (List.drop 47 kR) = false :=
  chainK (node 1 8) kR 47 1 48 rfl cr_47 qr_48
def k46 := kids (hdK (kR.drop 46)).1 (hdK (kR.drop 46)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail46_99 : anyK (node 1 7) (k46.drop 99) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part46_96 : anyK (node 1 7) ((k46.drop 96).take 3) = false := by decide +kernel
theorem tail46_96 : anyK (node 1 7) (k46.drop 96) = false := chainK _ _ 96 3 99 rfl part46_96 tail46_99
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part46_88 : anyK (node 1 7) ((k46.drop 88).take 8) = false := by decide +kernel
theorem tail46_88 : anyK (node 1 7) (k46.drop 88) = false := chainK _ _ 88 8 96 rfl part46_88 tail46_96
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part46_80 : anyK (node 1 7) ((k46.drop 80).take 8) = false := by decide +kernel
theorem tail46_80 : anyK (node 1 7) (k46.drop 80) = false := chainK _ _ 80 8 88 rfl part46_80 tail46_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part46_72 : anyK (node 1 7) ((k46.drop 72).take 8) = false := by decide +kernel
theorem tail46_72 : anyK (node 1 7) (k46.drop 72) = false := chainK _ _ 72 8 80 rfl part46_72 tail46_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part46_64 : anyK (node 1 7) ((k46.drop 64).take 8) = false := by decide +kernel
theorem tail46_64 : anyK (node 1 7) (k46.drop 64) = false := chainK _ _ 64 8 72 rfl part46_64 tail46_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part46_56 : anyK (node 1 7) ((k46.drop 56).take 8) = false := by decide +kernel
theorem tail46_56 : anyK (node 1 7) (k46.drop 56) = false := chainK _ _ 56 8 64 rfl part46_56 tail46_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part46_48 : anyK (node 1 7) ((k46.drop 48).take 8) = false := by decide +kernel
theorem tail46_48 : anyK (node 1 7) (k46.drop 48) = false := chainK _ _ 48 8 56 rfl part46_48 tail46_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part46_40 : anyK (node 1 7) ((k46.drop 40).take 8) = false := by decide +kernel
theorem tail46_40 : anyK (node 1 7) (k46.drop 40) = false := chainK _ _ 40 8 48 rfl part46_40 tail46_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part46_32 : anyK (node 1 7) ((k46.drop 32).take 8) = false := by decide +kernel
theorem tail46_32 : anyK (node 1 7) (k46.drop 32) = false := chainK _ _ 32 8 40 rfl part46_32 tail46_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part46_24 : anyK (node 1 7) ((k46.drop 24).take 8) = false := by decide +kernel
theorem tail46_24 : anyK (node 1 7) (k46.drop 24) = false := chainK _ _ 24 8 32 rfl part46_24 tail46_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part46_16 : anyK (node 1 7) ((k46.drop 16).take 8) = false := by decide +kernel
theorem tail46_16 : anyK (node 1 7) (k46.drop 16) = false := chainK _ _ 16 8 24 rfl part46_16 tail46_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part46_8 : anyK (node 1 7) ((k46.drop 8).take 8) = false := by decide +kernel
theorem tail46_8 : anyK (node 1 7) (k46.drop 8) = false := chainK _ _ 8 8 16 rfl part46_8 tail46_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part46_0 : anyK (node 1 7) ((k46.drop 0).take 8) = false := by decide +kernel
theorem tail46_0 : anyK (node 1 7) (k46.drop 0) = false := chainK _ _ 0 8 8 rfl part46_0 tail46_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_46 : anyK (node 1 8) ((kR.drop 46).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k46 tail46_0))
theorem qr_46 : anyK (node 1 8) (List.drop 46 kR) = false :=
  chainK (node 1 8) kR 46 1 47 rfl cr_46 qr_47
def k45 := kids (hdK (kR.drop 45)).1 (hdK (kR.drop 45)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail45_49 : anyK (node 1 7) (k45.drop 49) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part45_48 : anyK (node 1 7) ((k45.drop 48).take 1) = false := by decide +kernel
theorem tail45_48 : anyK (node 1 7) (k45.drop 48) = false := chainK _ _ 48 1 49 rfl part45_48 tail45_49
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part45_40 : anyK (node 1 7) ((k45.drop 40).take 8) = false := by decide +kernel
theorem tail45_40 : anyK (node 1 7) (k45.drop 40) = false := chainK _ _ 40 8 48 rfl part45_40 tail45_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part45_32 : anyK (node 1 7) ((k45.drop 32).take 8) = false := by decide +kernel
theorem tail45_32 : anyK (node 1 7) (k45.drop 32) = false := chainK _ _ 32 8 40 rfl part45_32 tail45_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part45_24 : anyK (node 1 7) ((k45.drop 24).take 8) = false := by decide +kernel
theorem tail45_24 : anyK (node 1 7) (k45.drop 24) = false := chainK _ _ 24 8 32 rfl part45_24 tail45_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part45_16 : anyK (node 1 7) ((k45.drop 16).take 8) = false := by decide +kernel
theorem tail45_16 : anyK (node 1 7) (k45.drop 16) = false := chainK _ _ 16 8 24 rfl part45_16 tail45_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part45_8 : anyK (node 1 7) ((k45.drop 8).take 8) = false := by decide +kernel
theorem tail45_8 : anyK (node 1 7) (k45.drop 8) = false := chainK _ _ 8 8 16 rfl part45_8 tail45_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part45_0 : anyK (node 1 7) ((k45.drop 0).take 8) = false := by decide +kernel
theorem tail45_0 : anyK (node 1 7) (k45.drop 0) = false := chainK _ _ 0 8 8 rfl part45_0 tail45_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_45 : anyK (node 1 8) ((kR.drop 45).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k45 tail45_0))
theorem qr_45 : anyK (node 1 8) (List.drop 45 kR) = false :=
  chainK (node 1 8) kR 45 1 46 rfl cr_45 qr_46
def k44 := kids (hdK (kR.drop 44)).1 (hdK (kR.drop 44)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail44_63 : anyK (node 1 7) (k44.drop 63) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part44_56 : anyK (node 1 7) ((k44.drop 56).take 7) = false := by decide +kernel
theorem tail44_56 : anyK (node 1 7) (k44.drop 56) = false := chainK _ _ 56 7 63 rfl part44_56 tail44_63
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part44_48 : anyK (node 1 7) ((k44.drop 48).take 8) = false := by decide +kernel
theorem tail44_48 : anyK (node 1 7) (k44.drop 48) = false := chainK _ _ 48 8 56 rfl part44_48 tail44_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part44_40 : anyK (node 1 7) ((k44.drop 40).take 8) = false := by decide +kernel
theorem tail44_40 : anyK (node 1 7) (k44.drop 40) = false := chainK _ _ 40 8 48 rfl part44_40 tail44_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part44_32 : anyK (node 1 7) ((k44.drop 32).take 8) = false := by decide +kernel
theorem tail44_32 : anyK (node 1 7) (k44.drop 32) = false := chainK _ _ 32 8 40 rfl part44_32 tail44_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part44_24 : anyK (node 1 7) ((k44.drop 24).take 8) = false := by decide +kernel
theorem tail44_24 : anyK (node 1 7) (k44.drop 24) = false := chainK _ _ 24 8 32 rfl part44_24 tail44_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part44_16 : anyK (node 1 7) ((k44.drop 16).take 8) = false := by decide +kernel
theorem tail44_16 : anyK (node 1 7) (k44.drop 16) = false := chainK _ _ 16 8 24 rfl part44_16 tail44_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part44_8 : anyK (node 1 7) ((k44.drop 8).take 8) = false := by decide +kernel
theorem tail44_8 : anyK (node 1 7) (k44.drop 8) = false := chainK _ _ 8 8 16 rfl part44_8 tail44_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part44_0 : anyK (node 1 7) ((k44.drop 0).take 8) = false := by decide +kernel
theorem tail44_0 : anyK (node 1 7) (k44.drop 0) = false := chainK _ _ 0 8 8 rfl part44_0 tail44_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_44 : anyK (node 1 8) ((kR.drop 44).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k44 tail44_0))
theorem qr_44 : anyK (node 1 8) (List.drop 44 kR) = false :=
  chainK (node 1 8) kR 44 1 45 rfl cr_44 qr_45
def k43 := kids (hdK (kR.drop 43)).1 (hdK (kR.drop 43)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail43_71 : anyK (node 1 7) (k43.drop 71) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part43_64 : anyK (node 1 7) ((k43.drop 64).take 7) = false := by decide +kernel
theorem tail43_64 : anyK (node 1 7) (k43.drop 64) = false := chainK _ _ 64 7 71 rfl part43_64 tail43_71
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part43_56 : anyK (node 1 7) ((k43.drop 56).take 8) = false := by decide +kernel
theorem tail43_56 : anyK (node 1 7) (k43.drop 56) = false := chainK _ _ 56 8 64 rfl part43_56 tail43_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part43_48 : anyK (node 1 7) ((k43.drop 48).take 8) = false := by decide +kernel
theorem tail43_48 : anyK (node 1 7) (k43.drop 48) = false := chainK _ _ 48 8 56 rfl part43_48 tail43_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part43_40 : anyK (node 1 7) ((k43.drop 40).take 8) = false := by decide +kernel
theorem tail43_40 : anyK (node 1 7) (k43.drop 40) = false := chainK _ _ 40 8 48 rfl part43_40 tail43_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part43_32 : anyK (node 1 7) ((k43.drop 32).take 8) = false := by decide +kernel
theorem tail43_32 : anyK (node 1 7) (k43.drop 32) = false := chainK _ _ 32 8 40 rfl part43_32 tail43_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part43_24 : anyK (node 1 7) ((k43.drop 24).take 8) = false := by decide +kernel
theorem tail43_24 : anyK (node 1 7) (k43.drop 24) = false := chainK _ _ 24 8 32 rfl part43_24 tail43_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part43_16 : anyK (node 1 7) ((k43.drop 16).take 8) = false := by decide +kernel
theorem tail43_16 : anyK (node 1 7) (k43.drop 16) = false := chainK _ _ 16 8 24 rfl part43_16 tail43_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part43_8 : anyK (node 1 7) ((k43.drop 8).take 8) = false := by decide +kernel
theorem tail43_8 : anyK (node 1 7) (k43.drop 8) = false := chainK _ _ 8 8 16 rfl part43_8 tail43_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part43_0 : anyK (node 1 7) ((k43.drop 0).take 8) = false := by decide +kernel
theorem tail43_0 : anyK (node 1 7) (k43.drop 0) = false := chainK _ _ 0 8 8 rfl part43_0 tail43_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_43 : anyK (node 1 8) ((kR.drop 43).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k43 tail43_0))
theorem qr_43 : anyK (node 1 8) (List.drop 43 kR) = false :=
  chainK (node 1 8) kR 43 1 44 rfl cr_43 qr_44
def k42 := kids (hdK (kR.drop 42)).1 (hdK (kR.drop 42)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail42_56 : anyK (node 1 7) (k42.drop 56) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part42_48 : anyK (node 1 7) ((k42.drop 48).take 8) = false := by decide +kernel
theorem tail42_48 : anyK (node 1 7) (k42.drop 48) = false := chainK _ _ 48 8 56 rfl part42_48 tail42_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part42_40 : anyK (node 1 7) ((k42.drop 40).take 8) = false := by decide +kernel
theorem tail42_40 : anyK (node 1 7) (k42.drop 40) = false := chainK _ _ 40 8 48 rfl part42_40 tail42_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part42_32 : anyK (node 1 7) ((k42.drop 32).take 8) = false := by decide +kernel
theorem tail42_32 : anyK (node 1 7) (k42.drop 32) = false := chainK _ _ 32 8 40 rfl part42_32 tail42_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part42_24 : anyK (node 1 7) ((k42.drop 24).take 8) = false := by decide +kernel
theorem tail42_24 : anyK (node 1 7) (k42.drop 24) = false := chainK _ _ 24 8 32 rfl part42_24 tail42_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part42_16 : anyK (node 1 7) ((k42.drop 16).take 8) = false := by decide +kernel
theorem tail42_16 : anyK (node 1 7) (k42.drop 16) = false := chainK _ _ 16 8 24 rfl part42_16 tail42_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part42_8 : anyK (node 1 7) ((k42.drop 8).take 8) = false := by decide +kernel
theorem tail42_8 : anyK (node 1 7) (k42.drop 8) = false := chainK _ _ 8 8 16 rfl part42_8 tail42_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part42_0 : anyK (node 1 7) ((k42.drop 0).take 8) = false := by decide +kernel
theorem tail42_0 : anyK (node 1 7) (k42.drop 0) = false := chainK _ _ 0 8 8 rfl part42_0 tail42_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_42 : anyK (node 1 8) ((kR.drop 42).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k42 tail42_0))
theorem qr_42 : anyK (node 1 8) (List.drop 42 kR) = false :=
  chainK (node 1 8) kR 42 1 43 rfl cr_42 qr_43
def k41 := kids (hdK (kR.drop 41)).1 (hdK (kR.drop 41)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail41_49 : anyK (node 1 7) (k41.drop 49) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part41_48 : anyK (node 1 7) ((k41.drop 48).take 1) = false := by decide +kernel
theorem tail41_48 : anyK (node 1 7) (k41.drop 48) = false := chainK _ _ 48 1 49 rfl part41_48 tail41_49
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part41_40 : anyK (node 1 7) ((k41.drop 40).take 8) = false := by decide +kernel
theorem tail41_40 : anyK (node 1 7) (k41.drop 40) = false := chainK _ _ 40 8 48 rfl part41_40 tail41_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part41_32 : anyK (node 1 7) ((k41.drop 32).take 8) = false := by decide +kernel
theorem tail41_32 : anyK (node 1 7) (k41.drop 32) = false := chainK _ _ 32 8 40 rfl part41_32 tail41_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part41_24 : anyK (node 1 7) ((k41.drop 24).take 8) = false := by decide +kernel
theorem tail41_24 : anyK (node 1 7) (k41.drop 24) = false := chainK _ _ 24 8 32 rfl part41_24 tail41_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part41_16 : anyK (node 1 7) ((k41.drop 16).take 8) = false := by decide +kernel
theorem tail41_16 : anyK (node 1 7) (k41.drop 16) = false := chainK _ _ 16 8 24 rfl part41_16 tail41_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part41_8 : anyK (node 1 7) ((k41.drop 8).take 8) = false := by decide +kernel
theorem tail41_8 : anyK (node 1 7) (k41.drop 8) = false := chainK _ _ 8 8 16 rfl part41_8 tail41_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part41_0 : anyK (node 1 7) ((k41.drop 0).take 8) = false := by decide +kernel
theorem tail41_0 : anyK (node 1 7) (k41.drop 0) = false := chainK _ _ 0 8 8 rfl part41_0 tail41_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_41 : anyK (node 1 8) ((kR.drop 41).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k41 tail41_0))
theorem qr_41 : anyK (node 1 8) (List.drop 41 kR) = false :=
  chainK (node 1 8) kR 41 1 42 rfl cr_41 qr_42
def k40 := kids (hdK (kR.drop 40)).1 (hdK (kR.drop 40)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail40_102 : anyK (node 1 7) (k40.drop 102) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part40_96 : anyK (node 1 7) ((k40.drop 96).take 6) = false := by decide +kernel
theorem tail40_96 : anyK (node 1 7) (k40.drop 96) = false := chainK _ _ 96 6 102 rfl part40_96 tail40_102
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part40_88 : anyK (node 1 7) ((k40.drop 88).take 8) = false := by decide +kernel
theorem tail40_88 : anyK (node 1 7) (k40.drop 88) = false := chainK _ _ 88 8 96 rfl part40_88 tail40_96
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part40_80 : anyK (node 1 7) ((k40.drop 80).take 8) = false := by decide +kernel
theorem tail40_80 : anyK (node 1 7) (k40.drop 80) = false := chainK _ _ 80 8 88 rfl part40_80 tail40_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part40_72 : anyK (node 1 7) ((k40.drop 72).take 8) = false := by decide +kernel
theorem tail40_72 : anyK (node 1 7) (k40.drop 72) = false := chainK _ _ 72 8 80 rfl part40_72 tail40_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part40_64 : anyK (node 1 7) ((k40.drop 64).take 8) = false := by decide +kernel
theorem tail40_64 : anyK (node 1 7) (k40.drop 64) = false := chainK _ _ 64 8 72 rfl part40_64 tail40_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part40_56 : anyK (node 1 7) ((k40.drop 56).take 8) = false := by decide +kernel
theorem tail40_56 : anyK (node 1 7) (k40.drop 56) = false := chainK _ _ 56 8 64 rfl part40_56 tail40_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part40_48 : anyK (node 1 7) ((k40.drop 48).take 8) = false := by decide +kernel
theorem tail40_48 : anyK (node 1 7) (k40.drop 48) = false := chainK _ _ 48 8 56 rfl part40_48 tail40_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part40_40 : anyK (node 1 7) ((k40.drop 40).take 8) = false := by decide +kernel
theorem tail40_40 : anyK (node 1 7) (k40.drop 40) = false := chainK _ _ 40 8 48 rfl part40_40 tail40_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part40_32 : anyK (node 1 7) ((k40.drop 32).take 8) = false := by decide +kernel
theorem tail40_32 : anyK (node 1 7) (k40.drop 32) = false := chainK _ _ 32 8 40 rfl part40_32 tail40_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part40_24 : anyK (node 1 7) ((k40.drop 24).take 8) = false := by decide +kernel
theorem tail40_24 : anyK (node 1 7) (k40.drop 24) = false := chainK _ _ 24 8 32 rfl part40_24 tail40_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part40_16 : anyK (node 1 7) ((k40.drop 16).take 8) = false := by decide +kernel
theorem tail40_16 : anyK (node 1 7) (k40.drop 16) = false := chainK _ _ 16 8 24 rfl part40_16 tail40_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part40_8 : anyK (node 1 7) ((k40.drop 8).take 8) = false := by decide +kernel
theorem tail40_8 : anyK (node 1 7) (k40.drop 8) = false := chainK _ _ 8 8 16 rfl part40_8 tail40_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part40_0 : anyK (node 1 7) ((k40.drop 0).take 8) = false := by decide +kernel
theorem tail40_0 : anyK (node 1 7) (k40.drop 0) = false := chainK _ _ 0 8 8 rfl part40_0 tail40_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_40 : anyK (node 1 8) ((kR.drop 40).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k40 tail40_0))
theorem qr_40 : anyK (node 1 8) (List.drop 40 kR) = false :=
  chainK (node 1 8) kR 40 1 41 rfl cr_40 qr_41
def k39 := kids (hdK (kR.drop 39)).1 (hdK (kR.drop 39)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail39_68 : anyK (node 1 7) (k39.drop 68) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part39_64 : anyK (node 1 7) ((k39.drop 64).take 4) = false := by decide +kernel
theorem tail39_64 : anyK (node 1 7) (k39.drop 64) = false := chainK _ _ 64 4 68 rfl part39_64 tail39_68
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part39_56 : anyK (node 1 7) ((k39.drop 56).take 8) = false := by decide +kernel
theorem tail39_56 : anyK (node 1 7) (k39.drop 56) = false := chainK _ _ 56 8 64 rfl part39_56 tail39_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part39_48 : anyK (node 1 7) ((k39.drop 48).take 8) = false := by decide +kernel
theorem tail39_48 : anyK (node 1 7) (k39.drop 48) = false := chainK _ _ 48 8 56 rfl part39_48 tail39_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part39_40 : anyK (node 1 7) ((k39.drop 40).take 8) = false := by decide +kernel
theorem tail39_40 : anyK (node 1 7) (k39.drop 40) = false := chainK _ _ 40 8 48 rfl part39_40 tail39_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part39_32 : anyK (node 1 7) ((k39.drop 32).take 8) = false := by decide +kernel
theorem tail39_32 : anyK (node 1 7) (k39.drop 32) = false := chainK _ _ 32 8 40 rfl part39_32 tail39_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part39_24 : anyK (node 1 7) ((k39.drop 24).take 8) = false := by decide +kernel
theorem tail39_24 : anyK (node 1 7) (k39.drop 24) = false := chainK _ _ 24 8 32 rfl part39_24 tail39_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part39_16 : anyK (node 1 7) ((k39.drop 16).take 8) = false := by decide +kernel
theorem tail39_16 : anyK (node 1 7) (k39.drop 16) = false := chainK _ _ 16 8 24 rfl part39_16 tail39_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part39_8 : anyK (node 1 7) ((k39.drop 8).take 8) = false := by decide +kernel
theorem tail39_8 : anyK (node 1 7) (k39.drop 8) = false := chainK _ _ 8 8 16 rfl part39_8 tail39_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part39_0 : anyK (node 1 7) ((k39.drop 0).take 8) = false := by decide +kernel
theorem tail39_0 : anyK (node 1 7) (k39.drop 0) = false := chainK _ _ 0 8 8 rfl part39_0 tail39_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_39 : anyK (node 1 8) ((kR.drop 39).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k39 tail39_0))
theorem qr_39 : anyK (node 1 8) (List.drop 39 kR) = false :=
  chainK (node 1 8) kR 39 1 40 rfl cr_39 qr_40
def k38 := kids (hdK (kR.drop 38)).1 (hdK (kR.drop 38)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail38_55 : anyK (node 1 7) (k38.drop 55) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part38_48 : anyK (node 1 7) ((k38.drop 48).take 7) = false := by decide +kernel
theorem tail38_48 : anyK (node 1 7) (k38.drop 48) = false := chainK _ _ 48 7 55 rfl part38_48 tail38_55
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part38_40 : anyK (node 1 7) ((k38.drop 40).take 8) = false := by decide +kernel
theorem tail38_40 : anyK (node 1 7) (k38.drop 40) = false := chainK _ _ 40 8 48 rfl part38_40 tail38_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part38_32 : anyK (node 1 7) ((k38.drop 32).take 8) = false := by decide +kernel
theorem tail38_32 : anyK (node 1 7) (k38.drop 32) = false := chainK _ _ 32 8 40 rfl part38_32 tail38_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part38_24 : anyK (node 1 7) ((k38.drop 24).take 8) = false := by decide +kernel
theorem tail38_24 : anyK (node 1 7) (k38.drop 24) = false := chainK _ _ 24 8 32 rfl part38_24 tail38_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part38_16 : anyK (node 1 7) ((k38.drop 16).take 8) = false := by decide +kernel
theorem tail38_16 : anyK (node 1 7) (k38.drop 16) = false := chainK _ _ 16 8 24 rfl part38_16 tail38_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part38_8 : anyK (node 1 7) ((k38.drop 8).take 8) = false := by decide +kernel
theorem tail38_8 : anyK (node 1 7) (k38.drop 8) = false := chainK _ _ 8 8 16 rfl part38_8 tail38_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part38_0 : anyK (node 1 7) ((k38.drop 0).take 8) = false := by decide +kernel
theorem tail38_0 : anyK (node 1 7) (k38.drop 0) = false := chainK _ _ 0 8 8 rfl part38_0 tail38_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_38 : anyK (node 1 8) ((kR.drop 38).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k38 tail38_0))
theorem qr_38 : anyK (node 1 8) (List.drop 38 kR) = false :=
  chainK (node 1 8) kR 38 1 39 rfl cr_38 qr_39
def k37 := kids (hdK (kR.drop 37)).1 (hdK (kR.drop 37)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail37_46 : anyK (node 1 7) (k37.drop 46) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part37_40 : anyK (node 1 7) ((k37.drop 40).take 6) = false := by decide +kernel
theorem tail37_40 : anyK (node 1 7) (k37.drop 40) = false := chainK _ _ 40 6 46 rfl part37_40 tail37_46
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part37_32 : anyK (node 1 7) ((k37.drop 32).take 8) = false := by decide +kernel
theorem tail37_32 : anyK (node 1 7) (k37.drop 32) = false := chainK _ _ 32 8 40 rfl part37_32 tail37_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part37_24 : anyK (node 1 7) ((k37.drop 24).take 8) = false := by decide +kernel
theorem tail37_24 : anyK (node 1 7) (k37.drop 24) = false := chainK _ _ 24 8 32 rfl part37_24 tail37_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part37_16 : anyK (node 1 7) ((k37.drop 16).take 8) = false := by decide +kernel
theorem tail37_16 : anyK (node 1 7) (k37.drop 16) = false := chainK _ _ 16 8 24 rfl part37_16 tail37_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part37_8 : anyK (node 1 7) ((k37.drop 8).take 8) = false := by decide +kernel
theorem tail37_8 : anyK (node 1 7) (k37.drop 8) = false := chainK _ _ 8 8 16 rfl part37_8 tail37_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part37_0 : anyK (node 1 7) ((k37.drop 0).take 8) = false := by decide +kernel
theorem tail37_0 : anyK (node 1 7) (k37.drop 0) = false := chainK _ _ 0 8 8 rfl part37_0 tail37_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_37 : anyK (node 1 8) ((kR.drop 37).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k37 tail37_0))
theorem qr_37 : anyK (node 1 8) (List.drop 37 kR) = false :=
  chainK (node 1 8) kR 37 1 38 rfl cr_37 qr_38
def k36 := kids (hdK (kR.drop 36)).1 (hdK (kR.drop 36)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail36_107 : anyK (node 1 7) (k36.drop 107) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part36_104 : anyK (node 1 7) ((k36.drop 104).take 3) = false := by decide +kernel
theorem tail36_104 : anyK (node 1 7) (k36.drop 104) = false := chainK _ _ 104 3 107 rfl part36_104 tail36_107
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part36_96 : anyK (node 1 7) ((k36.drop 96).take 8) = false := by decide +kernel
theorem tail36_96 : anyK (node 1 7) (k36.drop 96) = false := chainK _ _ 96 8 104 rfl part36_96 tail36_104
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part36_88 : anyK (node 1 7) ((k36.drop 88).take 8) = false := by decide +kernel
theorem tail36_88 : anyK (node 1 7) (k36.drop 88) = false := chainK _ _ 88 8 96 rfl part36_88 tail36_96
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part36_80 : anyK (node 1 7) ((k36.drop 80).take 8) = false := by decide +kernel
theorem tail36_80 : anyK (node 1 7) (k36.drop 80) = false := chainK _ _ 80 8 88 rfl part36_80 tail36_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part36_72 : anyK (node 1 7) ((k36.drop 72).take 8) = false := by decide +kernel
theorem tail36_72 : anyK (node 1 7) (k36.drop 72) = false := chainK _ _ 72 8 80 rfl part36_72 tail36_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part36_64 : anyK (node 1 7) ((k36.drop 64).take 8) = false := by decide +kernel
theorem tail36_64 : anyK (node 1 7) (k36.drop 64) = false := chainK _ _ 64 8 72 rfl part36_64 tail36_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part36_56 : anyK (node 1 7) ((k36.drop 56).take 8) = false := by decide +kernel
theorem tail36_56 : anyK (node 1 7) (k36.drop 56) = false := chainK _ _ 56 8 64 rfl part36_56 tail36_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part36_48 : anyK (node 1 7) ((k36.drop 48).take 8) = false := by decide +kernel
theorem tail36_48 : anyK (node 1 7) (k36.drop 48) = false := chainK _ _ 48 8 56 rfl part36_48 tail36_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part36_40 : anyK (node 1 7) ((k36.drop 40).take 8) = false := by decide +kernel
theorem tail36_40 : anyK (node 1 7) (k36.drop 40) = false := chainK _ _ 40 8 48 rfl part36_40 tail36_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part36_32 : anyK (node 1 7) ((k36.drop 32).take 8) = false := by decide +kernel
theorem tail36_32 : anyK (node 1 7) (k36.drop 32) = false := chainK _ _ 32 8 40 rfl part36_32 tail36_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part36_24 : anyK (node 1 7) ((k36.drop 24).take 8) = false := by decide +kernel
theorem tail36_24 : anyK (node 1 7) (k36.drop 24) = false := chainK _ _ 24 8 32 rfl part36_24 tail36_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part36_16 : anyK (node 1 7) ((k36.drop 16).take 8) = false := by decide +kernel
theorem tail36_16 : anyK (node 1 7) (k36.drop 16) = false := chainK _ _ 16 8 24 rfl part36_16 tail36_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part36_8 : anyK (node 1 7) ((k36.drop 8).take 8) = false := by decide +kernel
theorem tail36_8 : anyK (node 1 7) (k36.drop 8) = false := chainK _ _ 8 8 16 rfl part36_8 tail36_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part36_0 : anyK (node 1 7) ((k36.drop 0).take 8) = false := by decide +kernel
theorem tail36_0 : anyK (node 1 7) (k36.drop 0) = false := chainK _ _ 0 8 8 rfl part36_0 tail36_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_36 : anyK (node 1 8) ((kR.drop 36).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k36 tail36_0))
theorem qr_36 : anyK (node 1 8) (List.drop 36 kR) = false :=
  chainK (node 1 8) kR 36 1 37 rfl cr_36 qr_37
def k35 := kids (hdK (kR.drop 35)).1 (hdK (kR.drop 35)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail35_54 : anyK (node 1 7) (k35.drop 54) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part35_48 : anyK (node 1 7) ((k35.drop 48).take 6) = false := by decide +kernel
theorem tail35_48 : anyK (node 1 7) (k35.drop 48) = false := chainK _ _ 48 6 54 rfl part35_48 tail35_54
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part35_40 : anyK (node 1 7) ((k35.drop 40).take 8) = false := by decide +kernel
theorem tail35_40 : anyK (node 1 7) (k35.drop 40) = false := chainK _ _ 40 8 48 rfl part35_40 tail35_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part35_32 : anyK (node 1 7) ((k35.drop 32).take 8) = false := by decide +kernel
theorem tail35_32 : anyK (node 1 7) (k35.drop 32) = false := chainK _ _ 32 8 40 rfl part35_32 tail35_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part35_24 : anyK (node 1 7) ((k35.drop 24).take 8) = false := by decide +kernel
theorem tail35_24 : anyK (node 1 7) (k35.drop 24) = false := chainK _ _ 24 8 32 rfl part35_24 tail35_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part35_16 : anyK (node 1 7) ((k35.drop 16).take 8) = false := by decide +kernel
theorem tail35_16 : anyK (node 1 7) (k35.drop 16) = false := chainK _ _ 16 8 24 rfl part35_16 tail35_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part35_8 : anyK (node 1 7) ((k35.drop 8).take 8) = false := by decide +kernel
theorem tail35_8 : anyK (node 1 7) (k35.drop 8) = false := chainK _ _ 8 8 16 rfl part35_8 tail35_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part35_0 : anyK (node 1 7) ((k35.drop 0).take 8) = false := by decide +kernel
theorem tail35_0 : anyK (node 1 7) (k35.drop 0) = false := chainK _ _ 0 8 8 rfl part35_0 tail35_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_35 : anyK (node 1 8) ((kR.drop 35).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k35 tail35_0))
theorem qr_35 : anyK (node 1 8) (List.drop 35 kR) = false :=
  chainK (node 1 8) kR 35 1 36 rfl cr_35 qr_36
def k34 := kids (hdK (kR.drop 34)).1 (hdK (kR.drop 34)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail34_83 : anyK (node 1 7) (k34.drop 83) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part34_80 : anyK (node 1 7) ((k34.drop 80).take 3) = false := by decide +kernel
theorem tail34_80 : anyK (node 1 7) (k34.drop 80) = false := chainK _ _ 80 3 83 rfl part34_80 tail34_83
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part34_72 : anyK (node 1 7) ((k34.drop 72).take 8) = false := by decide +kernel
theorem tail34_72 : anyK (node 1 7) (k34.drop 72) = false := chainK _ _ 72 8 80 rfl part34_72 tail34_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part34_64 : anyK (node 1 7) ((k34.drop 64).take 8) = false := by decide +kernel
theorem tail34_64 : anyK (node 1 7) (k34.drop 64) = false := chainK _ _ 64 8 72 rfl part34_64 tail34_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part34_56 : anyK (node 1 7) ((k34.drop 56).take 8) = false := by decide +kernel
theorem tail34_56 : anyK (node 1 7) (k34.drop 56) = false := chainK _ _ 56 8 64 rfl part34_56 tail34_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part34_48 : anyK (node 1 7) ((k34.drop 48).take 8) = false := by decide +kernel
theorem tail34_48 : anyK (node 1 7) (k34.drop 48) = false := chainK _ _ 48 8 56 rfl part34_48 tail34_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part34_40 : anyK (node 1 7) ((k34.drop 40).take 8) = false := by decide +kernel
theorem tail34_40 : anyK (node 1 7) (k34.drop 40) = false := chainK _ _ 40 8 48 rfl part34_40 tail34_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part34_32 : anyK (node 1 7) ((k34.drop 32).take 8) = false := by decide +kernel
theorem tail34_32 : anyK (node 1 7) (k34.drop 32) = false := chainK _ _ 32 8 40 rfl part34_32 tail34_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part34_24 : anyK (node 1 7) ((k34.drop 24).take 8) = false := by decide +kernel
theorem tail34_24 : anyK (node 1 7) (k34.drop 24) = false := chainK _ _ 24 8 32 rfl part34_24 tail34_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part34_16 : anyK (node 1 7) ((k34.drop 16).take 8) = false := by decide +kernel
theorem tail34_16 : anyK (node 1 7) (k34.drop 16) = false := chainK _ _ 16 8 24 rfl part34_16 tail34_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part34_8 : anyK (node 1 7) ((k34.drop 8).take 8) = false := by decide +kernel
theorem tail34_8 : anyK (node 1 7) (k34.drop 8) = false := chainK _ _ 8 8 16 rfl part34_8 tail34_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part34_0 : anyK (node 1 7) ((k34.drop 0).take 8) = false := by decide +kernel
theorem tail34_0 : anyK (node 1 7) (k34.drop 0) = false := chainK _ _ 0 8 8 rfl part34_0 tail34_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_34 : anyK (node 1 8) ((kR.drop 34).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k34 tail34_0))
theorem qr_34 : anyK (node 1 8) (List.drop 34 kR) = false :=
  chainK (node 1 8) kR 34 1 35 rfl cr_34 qr_35
def k33 := kids (hdK (kR.drop 33)).1 (hdK (kR.drop 33)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail33_43 : anyK (node 1 7) (k33.drop 43) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part33_40 : anyK (node 1 7) ((k33.drop 40).take 3) = false := by decide +kernel
theorem tail33_40 : anyK (node 1 7) (k33.drop 40) = false := chainK _ _ 40 3 43 rfl part33_40 tail33_43
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part33_32 : anyK (node 1 7) ((k33.drop 32).take 8) = false := by decide +kernel
theorem tail33_32 : anyK (node 1 7) (k33.drop 32) = false := chainK _ _ 32 8 40 rfl part33_32 tail33_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part33_24 : anyK (node 1 7) ((k33.drop 24).take 8) = false := by decide +kernel
theorem tail33_24 : anyK (node 1 7) (k33.drop 24) = false := chainK _ _ 24 8 32 rfl part33_24 tail33_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part33_16 : anyK (node 1 7) ((k33.drop 16).take 8) = false := by decide +kernel
theorem tail33_16 : anyK (node 1 7) (k33.drop 16) = false := chainK _ _ 16 8 24 rfl part33_16 tail33_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part33_8 : anyK (node 1 7) ((k33.drop 8).take 8) = false := by decide +kernel
theorem tail33_8 : anyK (node 1 7) (k33.drop 8) = false := chainK _ _ 8 8 16 rfl part33_8 tail33_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part33_0 : anyK (node 1 7) ((k33.drop 0).take 8) = false := by decide +kernel
theorem tail33_0 : anyK (node 1 7) (k33.drop 0) = false := chainK _ _ 0 8 8 rfl part33_0 tail33_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_33 : anyK (node 1 8) ((kR.drop 33).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k33 tail33_0))
theorem qr_33 : anyK (node 1 8) (List.drop 33 kR) = false :=
  chainK (node 1 8) kR 33 1 34 rfl cr_33 qr_34
def k32 := kids (hdK (kR.drop 32)).1 (hdK (kR.drop 32)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail32_98 : anyK (node 1 7) (k32.drop 98) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part32_96 : anyK (node 1 7) ((k32.drop 96).take 2) = false := by decide +kernel
theorem tail32_96 : anyK (node 1 7) (k32.drop 96) = false := chainK _ _ 96 2 98 rfl part32_96 tail32_98
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part32_88 : anyK (node 1 7) ((k32.drop 88).take 8) = false := by decide +kernel
theorem tail32_88 : anyK (node 1 7) (k32.drop 88) = false := chainK _ _ 88 8 96 rfl part32_88 tail32_96
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part32_80 : anyK (node 1 7) ((k32.drop 80).take 8) = false := by decide +kernel
theorem tail32_80 : anyK (node 1 7) (k32.drop 80) = false := chainK _ _ 80 8 88 rfl part32_80 tail32_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part32_72 : anyK (node 1 7) ((k32.drop 72).take 8) = false := by decide +kernel
theorem tail32_72 : anyK (node 1 7) (k32.drop 72) = false := chainK _ _ 72 8 80 rfl part32_72 tail32_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part32_64 : anyK (node 1 7) ((k32.drop 64).take 8) = false := by decide +kernel
theorem tail32_64 : anyK (node 1 7) (k32.drop 64) = false := chainK _ _ 64 8 72 rfl part32_64 tail32_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part32_56 : anyK (node 1 7) ((k32.drop 56).take 8) = false := by decide +kernel
theorem tail32_56 : anyK (node 1 7) (k32.drop 56) = false := chainK _ _ 56 8 64 rfl part32_56 tail32_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part32_48 : anyK (node 1 7) ((k32.drop 48).take 8) = false := by decide +kernel
theorem tail32_48 : anyK (node 1 7) (k32.drop 48) = false := chainK _ _ 48 8 56 rfl part32_48 tail32_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part32_40 : anyK (node 1 7) ((k32.drop 40).take 8) = false := by decide +kernel
theorem tail32_40 : anyK (node 1 7) (k32.drop 40) = false := chainK _ _ 40 8 48 rfl part32_40 tail32_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part32_32 : anyK (node 1 7) ((k32.drop 32).take 8) = false := by decide +kernel
theorem tail32_32 : anyK (node 1 7) (k32.drop 32) = false := chainK _ _ 32 8 40 rfl part32_32 tail32_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part32_24 : anyK (node 1 7) ((k32.drop 24).take 8) = false := by decide +kernel
theorem tail32_24 : anyK (node 1 7) (k32.drop 24) = false := chainK _ _ 24 8 32 rfl part32_24 tail32_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part32_16 : anyK (node 1 7) ((k32.drop 16).take 8) = false := by decide +kernel
theorem tail32_16 : anyK (node 1 7) (k32.drop 16) = false := chainK _ _ 16 8 24 rfl part32_16 tail32_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part32_8 : anyK (node 1 7) ((k32.drop 8).take 8) = false := by decide +kernel
theorem tail32_8 : anyK (node 1 7) (k32.drop 8) = false := chainK _ _ 8 8 16 rfl part32_8 tail32_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part32_0 : anyK (node 1 7) ((k32.drop 0).take 8) = false := by decide +kernel
theorem tail32_0 : anyK (node 1 7) (k32.drop 0) = false := chainK _ _ 0 8 8 rfl part32_0 tail32_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_32 : anyK (node 1 8) ((kR.drop 32).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k32 tail32_0))
theorem qr_32 : anyK (node 1 8) (List.drop 32 kR) = false :=
  chainK (node 1 8) kR 32 1 33 rfl cr_32 qr_33
def k31 := kids (hdK (kR.drop 31)).1 (hdK (kR.drop 31)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail31_72 : anyK (node 1 7) (k31.drop 72) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part31_64 : anyK (node 1 7) ((k31.drop 64).take 8) = false := by decide +kernel
theorem tail31_64 : anyK (node 1 7) (k31.drop 64) = false := chainK _ _ 64 8 72 rfl part31_64 tail31_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part31_56 : anyK (node 1 7) ((k31.drop 56).take 8) = false := by decide +kernel
theorem tail31_56 : anyK (node 1 7) (k31.drop 56) = false := chainK _ _ 56 8 64 rfl part31_56 tail31_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part31_48 : anyK (node 1 7) ((k31.drop 48).take 8) = false := by decide +kernel
theorem tail31_48 : anyK (node 1 7) (k31.drop 48) = false := chainK _ _ 48 8 56 rfl part31_48 tail31_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part31_40 : anyK (node 1 7) ((k31.drop 40).take 8) = false := by decide +kernel
theorem tail31_40 : anyK (node 1 7) (k31.drop 40) = false := chainK _ _ 40 8 48 rfl part31_40 tail31_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part31_32 : anyK (node 1 7) ((k31.drop 32).take 8) = false := by decide +kernel
theorem tail31_32 : anyK (node 1 7) (k31.drop 32) = false := chainK _ _ 32 8 40 rfl part31_32 tail31_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part31_24 : anyK (node 1 7) ((k31.drop 24).take 8) = false := by decide +kernel
theorem tail31_24 : anyK (node 1 7) (k31.drop 24) = false := chainK _ _ 24 8 32 rfl part31_24 tail31_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part31_16 : anyK (node 1 7) ((k31.drop 16).take 8) = false := by decide +kernel
theorem tail31_16 : anyK (node 1 7) (k31.drop 16) = false := chainK _ _ 16 8 24 rfl part31_16 tail31_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part31_8 : anyK (node 1 7) ((k31.drop 8).take 8) = false := by decide +kernel
theorem tail31_8 : anyK (node 1 7) (k31.drop 8) = false := chainK _ _ 8 8 16 rfl part31_8 tail31_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part31_0 : anyK (node 1 7) ((k31.drop 0).take 8) = false := by decide +kernel
theorem tail31_0 : anyK (node 1 7) (k31.drop 0) = false := chainK _ _ 0 8 8 rfl part31_0 tail31_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_31 : anyK (node 1 8) ((kR.drop 31).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k31 tail31_0))
theorem qr_31 : anyK (node 1 8) (List.drop 31 kR) = false :=
  chainK (node 1 8) kR 31 1 32 rfl cr_31 qr_32
def k30 := kids (hdK (kR.drop 30)).1 (hdK (kR.drop 30)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail30_83 : anyK (node 1 7) (k30.drop 83) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part30_80 : anyK (node 1 7) ((k30.drop 80).take 3) = false := by decide +kernel
theorem tail30_80 : anyK (node 1 7) (k30.drop 80) = false := chainK _ _ 80 3 83 rfl part30_80 tail30_83
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part30_72 : anyK (node 1 7) ((k30.drop 72).take 8) = false := by decide +kernel
theorem tail30_72 : anyK (node 1 7) (k30.drop 72) = false := chainK _ _ 72 8 80 rfl part30_72 tail30_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part30_64 : anyK (node 1 7) ((k30.drop 64).take 8) = false := by decide +kernel
theorem tail30_64 : anyK (node 1 7) (k30.drop 64) = false := chainK _ _ 64 8 72 rfl part30_64 tail30_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part30_56 : anyK (node 1 7) ((k30.drop 56).take 8) = false := by decide +kernel
theorem tail30_56 : anyK (node 1 7) (k30.drop 56) = false := chainK _ _ 56 8 64 rfl part30_56 tail30_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part30_48 : anyK (node 1 7) ((k30.drop 48).take 8) = false := by decide +kernel
theorem tail30_48 : anyK (node 1 7) (k30.drop 48) = false := chainK _ _ 48 8 56 rfl part30_48 tail30_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part30_40 : anyK (node 1 7) ((k30.drop 40).take 8) = false := by decide +kernel
theorem tail30_40 : anyK (node 1 7) (k30.drop 40) = false := chainK _ _ 40 8 48 rfl part30_40 tail30_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part30_32 : anyK (node 1 7) ((k30.drop 32).take 8) = false := by decide +kernel
theorem tail30_32 : anyK (node 1 7) (k30.drop 32) = false := chainK _ _ 32 8 40 rfl part30_32 tail30_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part30_24 : anyK (node 1 7) ((k30.drop 24).take 8) = false := by decide +kernel
theorem tail30_24 : anyK (node 1 7) (k30.drop 24) = false := chainK _ _ 24 8 32 rfl part30_24 tail30_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part30_16 : anyK (node 1 7) ((k30.drop 16).take 8) = false := by decide +kernel
theorem tail30_16 : anyK (node 1 7) (k30.drop 16) = false := chainK _ _ 16 8 24 rfl part30_16 tail30_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part30_8 : anyK (node 1 7) ((k30.drop 8).take 8) = false := by decide +kernel
theorem tail30_8 : anyK (node 1 7) (k30.drop 8) = false := chainK _ _ 8 8 16 rfl part30_8 tail30_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part30_0 : anyK (node 1 7) ((k30.drop 0).take 8) = false := by decide +kernel
theorem tail30_0 : anyK (node 1 7) (k30.drop 0) = false := chainK _ _ 0 8 8 rfl part30_0 tail30_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_30 : anyK (node 1 8) ((kR.drop 30).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k30 tail30_0))
theorem qr_30 : anyK (node 1 8) (List.drop 30 kR) = false :=
  chainK (node 1 8) kR 30 1 31 rfl cr_30 qr_31
def k29 := kids (hdK (kR.drop 29)).1 (hdK (kR.drop 29)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail29_62 : anyK (node 1 7) (k29.drop 62) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part29_56 : anyK (node 1 7) ((k29.drop 56).take 6) = false := by decide +kernel
theorem tail29_56 : anyK (node 1 7) (k29.drop 56) = false := chainK _ _ 56 6 62 rfl part29_56 tail29_62
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part29_48 : anyK (node 1 7) ((k29.drop 48).take 8) = false := by decide +kernel
theorem tail29_48 : anyK (node 1 7) (k29.drop 48) = false := chainK _ _ 48 8 56 rfl part29_48 tail29_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part29_40 : anyK (node 1 7) ((k29.drop 40).take 8) = false := by decide +kernel
theorem tail29_40 : anyK (node 1 7) (k29.drop 40) = false := chainK _ _ 40 8 48 rfl part29_40 tail29_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part29_32 : anyK (node 1 7) ((k29.drop 32).take 8) = false := by decide +kernel
theorem tail29_32 : anyK (node 1 7) (k29.drop 32) = false := chainK _ _ 32 8 40 rfl part29_32 tail29_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part29_24 : anyK (node 1 7) ((k29.drop 24).take 8) = false := by decide +kernel
theorem tail29_24 : anyK (node 1 7) (k29.drop 24) = false := chainK _ _ 24 8 32 rfl part29_24 tail29_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part29_16 : anyK (node 1 7) ((k29.drop 16).take 8) = false := by decide +kernel
theorem tail29_16 : anyK (node 1 7) (k29.drop 16) = false := chainK _ _ 16 8 24 rfl part29_16 tail29_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part29_8 : anyK (node 1 7) ((k29.drop 8).take 8) = false := by decide +kernel
theorem tail29_8 : anyK (node 1 7) (k29.drop 8) = false := chainK _ _ 8 8 16 rfl part29_8 tail29_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part29_0 : anyK (node 1 7) ((k29.drop 0).take 8) = false := by decide +kernel
theorem tail29_0 : anyK (node 1 7) (k29.drop 0) = false := chainK _ _ 0 8 8 rfl part29_0 tail29_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_29 : anyK (node 1 8) ((kR.drop 29).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k29 tail29_0))
theorem qr_29 : anyK (node 1 8) (List.drop 29 kR) = false :=
  chainK (node 1 8) kR 29 1 30 rfl cr_29 qr_30
def k28 := kids (hdK (kR.drop 28)).1 (hdK (kR.drop 28)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail28_97 : anyK (node 1 7) (k28.drop 97) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part28_96 : anyK (node 1 7) ((k28.drop 96).take 1) = false := by decide +kernel
theorem tail28_96 : anyK (node 1 7) (k28.drop 96) = false := chainK _ _ 96 1 97 rfl part28_96 tail28_97
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part28_88 : anyK (node 1 7) ((k28.drop 88).take 8) = false := by decide +kernel
theorem tail28_88 : anyK (node 1 7) (k28.drop 88) = false := chainK _ _ 88 8 96 rfl part28_88 tail28_96
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part28_80 : anyK (node 1 7) ((k28.drop 80).take 8) = false := by decide +kernel
theorem tail28_80 : anyK (node 1 7) (k28.drop 80) = false := chainK _ _ 80 8 88 rfl part28_80 tail28_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part28_72 : anyK (node 1 7) ((k28.drop 72).take 8) = false := by decide +kernel
theorem tail28_72 : anyK (node 1 7) (k28.drop 72) = false := chainK _ _ 72 8 80 rfl part28_72 tail28_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part28_64 : anyK (node 1 7) ((k28.drop 64).take 8) = false := by decide +kernel
theorem tail28_64 : anyK (node 1 7) (k28.drop 64) = false := chainK _ _ 64 8 72 rfl part28_64 tail28_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part28_56 : anyK (node 1 7) ((k28.drop 56).take 8) = false := by decide +kernel
theorem tail28_56 : anyK (node 1 7) (k28.drop 56) = false := chainK _ _ 56 8 64 rfl part28_56 tail28_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part28_48 : anyK (node 1 7) ((k28.drop 48).take 8) = false := by decide +kernel
theorem tail28_48 : anyK (node 1 7) (k28.drop 48) = false := chainK _ _ 48 8 56 rfl part28_48 tail28_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part28_40 : anyK (node 1 7) ((k28.drop 40).take 8) = false := by decide +kernel
theorem tail28_40 : anyK (node 1 7) (k28.drop 40) = false := chainK _ _ 40 8 48 rfl part28_40 tail28_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part28_32 : anyK (node 1 7) ((k28.drop 32).take 8) = false := by decide +kernel
theorem tail28_32 : anyK (node 1 7) (k28.drop 32) = false := chainK _ _ 32 8 40 rfl part28_32 tail28_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part28_24 : anyK (node 1 7) ((k28.drop 24).take 8) = false := by decide +kernel
theorem tail28_24 : anyK (node 1 7) (k28.drop 24) = false := chainK _ _ 24 8 32 rfl part28_24 tail28_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part28_16 : anyK (node 1 7) ((k28.drop 16).take 8) = false := by decide +kernel
theorem tail28_16 : anyK (node 1 7) (k28.drop 16) = false := chainK _ _ 16 8 24 rfl part28_16 tail28_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part28_8 : anyK (node 1 7) ((k28.drop 8).take 8) = false := by decide +kernel
theorem tail28_8 : anyK (node 1 7) (k28.drop 8) = false := chainK _ _ 8 8 16 rfl part28_8 tail28_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part28_0 : anyK (node 1 7) ((k28.drop 0).take 8) = false := by decide +kernel
theorem tail28_0 : anyK (node 1 7) (k28.drop 0) = false := chainK _ _ 0 8 8 rfl part28_0 tail28_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_28 : anyK (node 1 8) ((kR.drop 28).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k28 tail28_0))
theorem qr_28 : anyK (node 1 8) (List.drop 28 kR) = false :=
  chainK (node 1 8) kR 28 1 29 rfl cr_28 qr_29
def k27 := kids (hdK (kR.drop 27)).1 (hdK (kR.drop 27)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail27_76 : anyK (node 1 7) (k27.drop 76) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part27_72 : anyK (node 1 7) ((k27.drop 72).take 4) = false := by decide +kernel
theorem tail27_72 : anyK (node 1 7) (k27.drop 72) = false := chainK _ _ 72 4 76 rfl part27_72 tail27_76
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part27_64 : anyK (node 1 7) ((k27.drop 64).take 8) = false := by decide +kernel
theorem tail27_64 : anyK (node 1 7) (k27.drop 64) = false := chainK _ _ 64 8 72 rfl part27_64 tail27_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part27_56 : anyK (node 1 7) ((k27.drop 56).take 8) = false := by decide +kernel
theorem tail27_56 : anyK (node 1 7) (k27.drop 56) = false := chainK _ _ 56 8 64 rfl part27_56 tail27_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part27_48 : anyK (node 1 7) ((k27.drop 48).take 8) = false := by decide +kernel
theorem tail27_48 : anyK (node 1 7) (k27.drop 48) = false := chainK _ _ 48 8 56 rfl part27_48 tail27_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part27_40 : anyK (node 1 7) ((k27.drop 40).take 8) = false := by decide +kernel
theorem tail27_40 : anyK (node 1 7) (k27.drop 40) = false := chainK _ _ 40 8 48 rfl part27_40 tail27_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part27_32 : anyK (node 1 7) ((k27.drop 32).take 8) = false := by decide +kernel
theorem tail27_32 : anyK (node 1 7) (k27.drop 32) = false := chainK _ _ 32 8 40 rfl part27_32 tail27_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part27_24 : anyK (node 1 7) ((k27.drop 24).take 8) = false := by decide +kernel
theorem tail27_24 : anyK (node 1 7) (k27.drop 24) = false := chainK _ _ 24 8 32 rfl part27_24 tail27_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part27_16 : anyK (node 1 7) ((k27.drop 16).take 8) = false := by decide +kernel
theorem tail27_16 : anyK (node 1 7) (k27.drop 16) = false := chainK _ _ 16 8 24 rfl part27_16 tail27_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part27_8 : anyK (node 1 7) ((k27.drop 8).take 8) = false := by decide +kernel
theorem tail27_8 : anyK (node 1 7) (k27.drop 8) = false := chainK _ _ 8 8 16 rfl part27_8 tail27_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part27_0 : anyK (node 1 7) ((k27.drop 0).take 8) = false := by decide +kernel
theorem tail27_0 : anyK (node 1 7) (k27.drop 0) = false := chainK _ _ 0 8 8 rfl part27_0 tail27_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_27 : anyK (node 1 8) ((kR.drop 27).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k27 tail27_0))
theorem qr_27 : anyK (node 1 8) (List.drop 27 kR) = false :=
  chainK (node 1 8) kR 27 1 28 rfl cr_27 qr_28
def k26 := kids (hdK (kR.drop 26)).1 (hdK (kR.drop 26)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail26_99 : anyK (node 1 7) (k26.drop 99) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part26_96 : anyK (node 1 7) ((k26.drop 96).take 3) = false := by decide +kernel
theorem tail26_96 : anyK (node 1 7) (k26.drop 96) = false := chainK _ _ 96 3 99 rfl part26_96 tail26_99
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part26_88 : anyK (node 1 7) ((k26.drop 88).take 8) = false := by decide +kernel
theorem tail26_88 : anyK (node 1 7) (k26.drop 88) = false := chainK _ _ 88 8 96 rfl part26_88 tail26_96
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part26_80 : anyK (node 1 7) ((k26.drop 80).take 8) = false := by decide +kernel
theorem tail26_80 : anyK (node 1 7) (k26.drop 80) = false := chainK _ _ 80 8 88 rfl part26_80 tail26_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part26_72 : anyK (node 1 7) ((k26.drop 72).take 8) = false := by decide +kernel
theorem tail26_72 : anyK (node 1 7) (k26.drop 72) = false := chainK _ _ 72 8 80 rfl part26_72 tail26_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part26_64 : anyK (node 1 7) ((k26.drop 64).take 8) = false := by decide +kernel
theorem tail26_64 : anyK (node 1 7) (k26.drop 64) = false := chainK _ _ 64 8 72 rfl part26_64 tail26_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part26_56 : anyK (node 1 7) ((k26.drop 56).take 8) = false := by decide +kernel
theorem tail26_56 : anyK (node 1 7) (k26.drop 56) = false := chainK _ _ 56 8 64 rfl part26_56 tail26_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part26_48 : anyK (node 1 7) ((k26.drop 48).take 8) = false := by decide +kernel
theorem tail26_48 : anyK (node 1 7) (k26.drop 48) = false := chainK _ _ 48 8 56 rfl part26_48 tail26_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part26_40 : anyK (node 1 7) ((k26.drop 40).take 8) = false := by decide +kernel
theorem tail26_40 : anyK (node 1 7) (k26.drop 40) = false := chainK _ _ 40 8 48 rfl part26_40 tail26_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part26_32 : anyK (node 1 7) ((k26.drop 32).take 8) = false := by decide +kernel
theorem tail26_32 : anyK (node 1 7) (k26.drop 32) = false := chainK _ _ 32 8 40 rfl part26_32 tail26_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part26_24 : anyK (node 1 7) ((k26.drop 24).take 8) = false := by decide +kernel
theorem tail26_24 : anyK (node 1 7) (k26.drop 24) = false := chainK _ _ 24 8 32 rfl part26_24 tail26_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part26_16 : anyK (node 1 7) ((k26.drop 16).take 8) = false := by decide +kernel
theorem tail26_16 : anyK (node 1 7) (k26.drop 16) = false := chainK _ _ 16 8 24 rfl part26_16 tail26_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part26_8 : anyK (node 1 7) ((k26.drop 8).take 8) = false := by decide +kernel
theorem tail26_8 : anyK (node 1 7) (k26.drop 8) = false := chainK _ _ 8 8 16 rfl part26_8 tail26_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part26_0 : anyK (node 1 7) ((k26.drop 0).take 8) = false := by decide +kernel
theorem tail26_0 : anyK (node 1 7) (k26.drop 0) = false := chainK _ _ 0 8 8 rfl part26_0 tail26_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_26 : anyK (node 1 8) ((kR.drop 26).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k26 tail26_0))
theorem qr_26 : anyK (node 1 8) (List.drop 26 kR) = false :=
  chainK (node 1 8) kR 26 1 27 rfl cr_26 qr_27
def k25 := kids (hdK (kR.drop 25)).1 (hdK (kR.drop 25)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail25_64 : anyK (node 1 7) (k25.drop 64) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part25_56 : anyK (node 1 7) ((k25.drop 56).take 8) = false := by decide +kernel
theorem tail25_56 : anyK (node 1 7) (k25.drop 56) = false := chainK _ _ 56 8 64 rfl part25_56 tail25_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part25_48 : anyK (node 1 7) ((k25.drop 48).take 8) = false := by decide +kernel
theorem tail25_48 : anyK (node 1 7) (k25.drop 48) = false := chainK _ _ 48 8 56 rfl part25_48 tail25_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part25_40 : anyK (node 1 7) ((k25.drop 40).take 8) = false := by decide +kernel
theorem tail25_40 : anyK (node 1 7) (k25.drop 40) = false := chainK _ _ 40 8 48 rfl part25_40 tail25_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part25_32 : anyK (node 1 7) ((k25.drop 32).take 8) = false := by decide +kernel
theorem tail25_32 : anyK (node 1 7) (k25.drop 32) = false := chainK _ _ 32 8 40 rfl part25_32 tail25_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part25_24 : anyK (node 1 7) ((k25.drop 24).take 8) = false := by decide +kernel
theorem tail25_24 : anyK (node 1 7) (k25.drop 24) = false := chainK _ _ 24 8 32 rfl part25_24 tail25_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part25_16 : anyK (node 1 7) ((k25.drop 16).take 8) = false := by decide +kernel
theorem tail25_16 : anyK (node 1 7) (k25.drop 16) = false := chainK _ _ 16 8 24 rfl part25_16 tail25_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part25_8 : anyK (node 1 7) ((k25.drop 8).take 8) = false := by decide +kernel
theorem tail25_8 : anyK (node 1 7) (k25.drop 8) = false := chainK _ _ 8 8 16 rfl part25_8 tail25_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part25_0 : anyK (node 1 7) ((k25.drop 0).take 8) = false := by decide +kernel
theorem tail25_0 : anyK (node 1 7) (k25.drop 0) = false := chainK _ _ 0 8 8 rfl part25_0 tail25_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_25 : anyK (node 1 8) ((kR.drop 25).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k25 tail25_0))
theorem qr_25 : anyK (node 1 8) (List.drop 25 kR) = false :=
  chainK (node 1 8) kR 25 1 26 rfl cr_25 qr_26
def k24 := kids (hdK (kR.drop 24)).1 (hdK (kR.drop 24)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail24_88 : anyK (node 1 7) (k24.drop 88) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part24_80 : anyK (node 1 7) ((k24.drop 80).take 8) = false := by decide +kernel
theorem tail24_80 : anyK (node 1 7) (k24.drop 80) = false := chainK _ _ 80 8 88 rfl part24_80 tail24_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part24_72 : anyK (node 1 7) ((k24.drop 72).take 8) = false := by decide +kernel
theorem tail24_72 : anyK (node 1 7) (k24.drop 72) = false := chainK _ _ 72 8 80 rfl part24_72 tail24_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part24_64 : anyK (node 1 7) ((k24.drop 64).take 8) = false := by decide +kernel
theorem tail24_64 : anyK (node 1 7) (k24.drop 64) = false := chainK _ _ 64 8 72 rfl part24_64 tail24_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part24_56 : anyK (node 1 7) ((k24.drop 56).take 8) = false := by decide +kernel
theorem tail24_56 : anyK (node 1 7) (k24.drop 56) = false := chainK _ _ 56 8 64 rfl part24_56 tail24_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part24_48 : anyK (node 1 7) ((k24.drop 48).take 8) = false := by decide +kernel
theorem tail24_48 : anyK (node 1 7) (k24.drop 48) = false := chainK _ _ 48 8 56 rfl part24_48 tail24_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part24_40 : anyK (node 1 7) ((k24.drop 40).take 8) = false := by decide +kernel
theorem tail24_40 : anyK (node 1 7) (k24.drop 40) = false := chainK _ _ 40 8 48 rfl part24_40 tail24_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part24_32 : anyK (node 1 7) ((k24.drop 32).take 8) = false := by decide +kernel
theorem tail24_32 : anyK (node 1 7) (k24.drop 32) = false := chainK _ _ 32 8 40 rfl part24_32 tail24_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part24_24 : anyK (node 1 7) ((k24.drop 24).take 8) = false := by decide +kernel
theorem tail24_24 : anyK (node 1 7) (k24.drop 24) = false := chainK _ _ 24 8 32 rfl part24_24 tail24_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part24_16 : anyK (node 1 7) ((k24.drop 16).take 8) = false := by decide +kernel
theorem tail24_16 : anyK (node 1 7) (k24.drop 16) = false := chainK _ _ 16 8 24 rfl part24_16 tail24_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part24_8 : anyK (node 1 7) ((k24.drop 8).take 8) = false := by decide +kernel
theorem tail24_8 : anyK (node 1 7) (k24.drop 8) = false := chainK _ _ 8 8 16 rfl part24_8 tail24_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part24_0 : anyK (node 1 7) ((k24.drop 0).take 8) = false := by decide +kernel
theorem tail24_0 : anyK (node 1 7) (k24.drop 0) = false := chainK _ _ 0 8 8 rfl part24_0 tail24_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_24 : anyK (node 1 8) ((kR.drop 24).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k24 tail24_0))
theorem qr_24 : anyK (node 1 8) (List.drop 24 kR) = false :=
  chainK (node 1 8) kR 24 1 25 rfl cr_24 qr_25
def k23 := kids (hdK (kR.drop 23)).1 (hdK (kR.drop 23)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail23_59 : anyK (node 1 7) (k23.drop 59) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part23_56 : anyK (node 1 7) ((k23.drop 56).take 3) = false := by decide +kernel
theorem tail23_56 : anyK (node 1 7) (k23.drop 56) = false := chainK _ _ 56 3 59 rfl part23_56 tail23_59
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part23_48 : anyK (node 1 7) ((k23.drop 48).take 8) = false := by decide +kernel
theorem tail23_48 : anyK (node 1 7) (k23.drop 48) = false := chainK _ _ 48 8 56 rfl part23_48 tail23_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part23_40 : anyK (node 1 7) ((k23.drop 40).take 8) = false := by decide +kernel
theorem tail23_40 : anyK (node 1 7) (k23.drop 40) = false := chainK _ _ 40 8 48 rfl part23_40 tail23_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part23_32 : anyK (node 1 7) ((k23.drop 32).take 8) = false := by decide +kernel
theorem tail23_32 : anyK (node 1 7) (k23.drop 32) = false := chainK _ _ 32 8 40 rfl part23_32 tail23_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part23_24 : anyK (node 1 7) ((k23.drop 24).take 8) = false := by decide +kernel
theorem tail23_24 : anyK (node 1 7) (k23.drop 24) = false := chainK _ _ 24 8 32 rfl part23_24 tail23_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part23_16 : anyK (node 1 7) ((k23.drop 16).take 8) = false := by decide +kernel
theorem tail23_16 : anyK (node 1 7) (k23.drop 16) = false := chainK _ _ 16 8 24 rfl part23_16 tail23_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part23_8 : anyK (node 1 7) ((k23.drop 8).take 8) = false := by decide +kernel
theorem tail23_8 : anyK (node 1 7) (k23.drop 8) = false := chainK _ _ 8 8 16 rfl part23_8 tail23_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part23_0 : anyK (node 1 7) ((k23.drop 0).take 8) = false := by decide +kernel
theorem tail23_0 : anyK (node 1 7) (k23.drop 0) = false := chainK _ _ 0 8 8 rfl part23_0 tail23_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_23 : anyK (node 1 8) ((kR.drop 23).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k23 tail23_0))
theorem qr_23 : anyK (node 1 8) (List.drop 23 kR) = false :=
  chainK (node 1 8) kR 23 1 24 rfl cr_23 qr_24
def k22 := kids (hdK (kR.drop 22)).1 (hdK (kR.drop 22)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail22_84 : anyK (node 1 7) (k22.drop 84) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part22_80 : anyK (node 1 7) ((k22.drop 80).take 4) = false := by decide +kernel
theorem tail22_80 : anyK (node 1 7) (k22.drop 80) = false := chainK _ _ 80 4 84 rfl part22_80 tail22_84
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part22_72 : anyK (node 1 7) ((k22.drop 72).take 8) = false := by decide +kernel
theorem tail22_72 : anyK (node 1 7) (k22.drop 72) = false := chainK _ _ 72 8 80 rfl part22_72 tail22_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part22_64 : anyK (node 1 7) ((k22.drop 64).take 8) = false := by decide +kernel
theorem tail22_64 : anyK (node 1 7) (k22.drop 64) = false := chainK _ _ 64 8 72 rfl part22_64 tail22_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part22_56 : anyK (node 1 7) ((k22.drop 56).take 8) = false := by decide +kernel
theorem tail22_56 : anyK (node 1 7) (k22.drop 56) = false := chainK _ _ 56 8 64 rfl part22_56 tail22_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part22_48 : anyK (node 1 7) ((k22.drop 48).take 8) = false := by decide +kernel
theorem tail22_48 : anyK (node 1 7) (k22.drop 48) = false := chainK _ _ 48 8 56 rfl part22_48 tail22_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part22_40 : anyK (node 1 7) ((k22.drop 40).take 8) = false := by decide +kernel
theorem tail22_40 : anyK (node 1 7) (k22.drop 40) = false := chainK _ _ 40 8 48 rfl part22_40 tail22_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part22_32 : anyK (node 1 7) ((k22.drop 32).take 8) = false := by decide +kernel
theorem tail22_32 : anyK (node 1 7) (k22.drop 32) = false := chainK _ _ 32 8 40 rfl part22_32 tail22_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part22_24 : anyK (node 1 7) ((k22.drop 24).take 8) = false := by decide +kernel
theorem tail22_24 : anyK (node 1 7) (k22.drop 24) = false := chainK _ _ 24 8 32 rfl part22_24 tail22_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part22_16 : anyK (node 1 7) ((k22.drop 16).take 8) = false := by decide +kernel
theorem tail22_16 : anyK (node 1 7) (k22.drop 16) = false := chainK _ _ 16 8 24 rfl part22_16 tail22_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part22_8 : anyK (node 1 7) ((k22.drop 8).take 8) = false := by decide +kernel
theorem tail22_8 : anyK (node 1 7) (k22.drop 8) = false := chainK _ _ 8 8 16 rfl part22_8 tail22_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part22_0 : anyK (node 1 7) ((k22.drop 0).take 8) = false := by decide +kernel
theorem tail22_0 : anyK (node 1 7) (k22.drop 0) = false := chainK _ _ 0 8 8 rfl part22_0 tail22_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_22 : anyK (node 1 8) ((kR.drop 22).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k22 tail22_0))
theorem qr_22 : anyK (node 1 8) (List.drop 22 kR) = false :=
  chainK (node 1 8) kR 22 1 23 rfl cr_22 qr_23
def k21 := kids (hdK (kR.drop 21)).1 (hdK (kR.drop 21)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail21_51 : anyK (node 1 7) (k21.drop 51) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part21_48 : anyK (node 1 7) ((k21.drop 48).take 3) = false := by decide +kernel
theorem tail21_48 : anyK (node 1 7) (k21.drop 48) = false := chainK _ _ 48 3 51 rfl part21_48 tail21_51
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part21_40 : anyK (node 1 7) ((k21.drop 40).take 8) = false := by decide +kernel
theorem tail21_40 : anyK (node 1 7) (k21.drop 40) = false := chainK _ _ 40 8 48 rfl part21_40 tail21_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part21_32 : anyK (node 1 7) ((k21.drop 32).take 8) = false := by decide +kernel
theorem tail21_32 : anyK (node 1 7) (k21.drop 32) = false := chainK _ _ 32 8 40 rfl part21_32 tail21_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part21_24 : anyK (node 1 7) ((k21.drop 24).take 8) = false := by decide +kernel
theorem tail21_24 : anyK (node 1 7) (k21.drop 24) = false := chainK _ _ 24 8 32 rfl part21_24 tail21_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part21_16 : anyK (node 1 7) ((k21.drop 16).take 8) = false := by decide +kernel
theorem tail21_16 : anyK (node 1 7) (k21.drop 16) = false := chainK _ _ 16 8 24 rfl part21_16 tail21_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part21_8 : anyK (node 1 7) ((k21.drop 8).take 8) = false := by decide +kernel
theorem tail21_8 : anyK (node 1 7) (k21.drop 8) = false := chainK _ _ 8 8 16 rfl part21_8 tail21_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part21_0 : anyK (node 1 7) ((k21.drop 0).take 8) = false := by decide +kernel
theorem tail21_0 : anyK (node 1 7) (k21.drop 0) = false := chainK _ _ 0 8 8 rfl part21_0 tail21_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_21 : anyK (node 1 8) ((kR.drop 21).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k21 tail21_0))
theorem qr_21 : anyK (node 1 8) (List.drop 21 kR) = false :=
  chainK (node 1 8) kR 21 1 22 rfl cr_21 qr_22
def k20 := kids (hdK (kR.drop 20)).1 (hdK (kR.drop 20)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail20_103 : anyK (node 1 7) (k20.drop 103) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part20_96 : anyK (node 1 7) ((k20.drop 96).take 7) = false := by decide +kernel
theorem tail20_96 : anyK (node 1 7) (k20.drop 96) = false := chainK _ _ 96 7 103 rfl part20_96 tail20_103
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part20_88 : anyK (node 1 7) ((k20.drop 88).take 8) = false := by decide +kernel
theorem tail20_88 : anyK (node 1 7) (k20.drop 88) = false := chainK _ _ 88 8 96 rfl part20_88 tail20_96
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part20_80 : anyK (node 1 7) ((k20.drop 80).take 8) = false := by decide +kernel
theorem tail20_80 : anyK (node 1 7) (k20.drop 80) = false := chainK _ _ 80 8 88 rfl part20_80 tail20_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part20_72 : anyK (node 1 7) ((k20.drop 72).take 8) = false := by decide +kernel
theorem tail20_72 : anyK (node 1 7) (k20.drop 72) = false := chainK _ _ 72 8 80 rfl part20_72 tail20_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part20_64 : anyK (node 1 7) ((k20.drop 64).take 8) = false := by decide +kernel
theorem tail20_64 : anyK (node 1 7) (k20.drop 64) = false := chainK _ _ 64 8 72 rfl part20_64 tail20_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part20_56 : anyK (node 1 7) ((k20.drop 56).take 8) = false := by decide +kernel
theorem tail20_56 : anyK (node 1 7) (k20.drop 56) = false := chainK _ _ 56 8 64 rfl part20_56 tail20_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part20_48 : anyK (node 1 7) ((k20.drop 48).take 8) = false := by decide +kernel
theorem tail20_48 : anyK (node 1 7) (k20.drop 48) = false := chainK _ _ 48 8 56 rfl part20_48 tail20_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part20_40 : anyK (node 1 7) ((k20.drop 40).take 8) = false := by decide +kernel
theorem tail20_40 : anyK (node 1 7) (k20.drop 40) = false := chainK _ _ 40 8 48 rfl part20_40 tail20_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part20_32 : anyK (node 1 7) ((k20.drop 32).take 8) = false := by decide +kernel
theorem tail20_32 : anyK (node 1 7) (k20.drop 32) = false := chainK _ _ 32 8 40 rfl part20_32 tail20_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part20_24 : anyK (node 1 7) ((k20.drop 24).take 8) = false := by decide +kernel
theorem tail20_24 : anyK (node 1 7) (k20.drop 24) = false := chainK _ _ 24 8 32 rfl part20_24 tail20_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part20_16 : anyK (node 1 7) ((k20.drop 16).take 8) = false := by decide +kernel
theorem tail20_16 : anyK (node 1 7) (k20.drop 16) = false := chainK _ _ 16 8 24 rfl part20_16 tail20_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part20_8 : anyK (node 1 7) ((k20.drop 8).take 8) = false := by decide +kernel
theorem tail20_8 : anyK (node 1 7) (k20.drop 8) = false := chainK _ _ 8 8 16 rfl part20_8 tail20_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part20_0 : anyK (node 1 7) ((k20.drop 0).take 8) = false := by decide +kernel
theorem tail20_0 : anyK (node 1 7) (k20.drop 0) = false := chainK _ _ 0 8 8 rfl part20_0 tail20_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_20 : anyK (node 1 8) ((kR.drop 20).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k20 tail20_0))
theorem qr_20 : anyK (node 1 8) (List.drop 20 kR) = false :=
  chainK (node 1 8) kR 20 1 21 rfl cr_20 qr_21
def k19 := kids (hdK (kR.drop 19)).1 (hdK (kR.drop 19)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail19_51 : anyK (node 1 7) (k19.drop 51) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part19_48 : anyK (node 1 7) ((k19.drop 48).take 3) = false := by decide +kernel
theorem tail19_48 : anyK (node 1 7) (k19.drop 48) = false := chainK _ _ 48 3 51 rfl part19_48 tail19_51
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part19_40 : anyK (node 1 7) ((k19.drop 40).take 8) = false := by decide +kernel
theorem tail19_40 : anyK (node 1 7) (k19.drop 40) = false := chainK _ _ 40 8 48 rfl part19_40 tail19_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part19_32 : anyK (node 1 7) ((k19.drop 32).take 8) = false := by decide +kernel
theorem tail19_32 : anyK (node 1 7) (k19.drop 32) = false := chainK _ _ 32 8 40 rfl part19_32 tail19_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part19_24 : anyK (node 1 7) ((k19.drop 24).take 8) = false := by decide +kernel
theorem tail19_24 : anyK (node 1 7) (k19.drop 24) = false := chainK _ _ 24 8 32 rfl part19_24 tail19_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part19_16 : anyK (node 1 7) ((k19.drop 16).take 8) = false := by decide +kernel
theorem tail19_16 : anyK (node 1 7) (k19.drop 16) = false := chainK _ _ 16 8 24 rfl part19_16 tail19_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part19_8 : anyK (node 1 7) ((k19.drop 8).take 8) = false := by decide +kernel
theorem tail19_8 : anyK (node 1 7) (k19.drop 8) = false := chainK _ _ 8 8 16 rfl part19_8 tail19_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part19_0 : anyK (node 1 7) ((k19.drop 0).take 8) = false := by decide +kernel
theorem tail19_0 : anyK (node 1 7) (k19.drop 0) = false := chainK _ _ 0 8 8 rfl part19_0 tail19_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_19 : anyK (node 1 8) ((kR.drop 19).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k19 tail19_0))
theorem qr_19 : anyK (node 1 8) (List.drop 19 kR) = false :=
  chainK (node 1 8) kR 19 1 20 rfl cr_19 qr_20
def k18 := kids (hdK (kR.drop 18)).1 (hdK (kR.drop 18)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail18_93 : anyK (node 1 7) (k18.drop 93) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part18_88 : anyK (node 1 7) ((k18.drop 88).take 5) = false := by decide +kernel
theorem tail18_88 : anyK (node 1 7) (k18.drop 88) = false := chainK _ _ 88 5 93 rfl part18_88 tail18_93
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part18_80 : anyK (node 1 7) ((k18.drop 80).take 8) = false := by decide +kernel
theorem tail18_80 : anyK (node 1 7) (k18.drop 80) = false := chainK _ _ 80 8 88 rfl part18_80 tail18_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part18_72 : anyK (node 1 7) ((k18.drop 72).take 8) = false := by decide +kernel
theorem tail18_72 : anyK (node 1 7) (k18.drop 72) = false := chainK _ _ 72 8 80 rfl part18_72 tail18_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part18_64 : anyK (node 1 7) ((k18.drop 64).take 8) = false := by decide +kernel
theorem tail18_64 : anyK (node 1 7) (k18.drop 64) = false := chainK _ _ 64 8 72 rfl part18_64 tail18_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part18_56 : anyK (node 1 7) ((k18.drop 56).take 8) = false := by decide +kernel
theorem tail18_56 : anyK (node 1 7) (k18.drop 56) = false := chainK _ _ 56 8 64 rfl part18_56 tail18_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part18_48 : anyK (node 1 7) ((k18.drop 48).take 8) = false := by decide +kernel
theorem tail18_48 : anyK (node 1 7) (k18.drop 48) = false := chainK _ _ 48 8 56 rfl part18_48 tail18_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part18_40 : anyK (node 1 7) ((k18.drop 40).take 8) = false := by decide +kernel
theorem tail18_40 : anyK (node 1 7) (k18.drop 40) = false := chainK _ _ 40 8 48 rfl part18_40 tail18_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part18_32 : anyK (node 1 7) ((k18.drop 32).take 8) = false := by decide +kernel
theorem tail18_32 : anyK (node 1 7) (k18.drop 32) = false := chainK _ _ 32 8 40 rfl part18_32 tail18_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part18_24 : anyK (node 1 7) ((k18.drop 24).take 8) = false := by decide +kernel
theorem tail18_24 : anyK (node 1 7) (k18.drop 24) = false := chainK _ _ 24 8 32 rfl part18_24 tail18_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part18_16 : anyK (node 1 7) ((k18.drop 16).take 8) = false := by decide +kernel
theorem tail18_16 : anyK (node 1 7) (k18.drop 16) = false := chainK _ _ 16 8 24 rfl part18_16 tail18_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part18_8 : anyK (node 1 7) ((k18.drop 8).take 8) = false := by decide +kernel
theorem tail18_8 : anyK (node 1 7) (k18.drop 8) = false := chainK _ _ 8 8 16 rfl part18_8 tail18_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part18_0 : anyK (node 1 7) ((k18.drop 0).take 8) = false := by decide +kernel
theorem tail18_0 : anyK (node 1 7) (k18.drop 0) = false := chainK _ _ 0 8 8 rfl part18_0 tail18_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_18 : anyK (node 1 8) ((kR.drop 18).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k18 tail18_0))
theorem qr_18 : anyK (node 1 8) (List.drop 18 kR) = false :=
  chainK (node 1 8) kR 18 1 19 rfl cr_18 qr_19
def k17 := kids (hdK (kR.drop 17)).1 (hdK (kR.drop 17)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail17_48 : anyK (node 1 7) (k17.drop 48) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part17_40 : anyK (node 1 7) ((k17.drop 40).take 8) = false := by decide +kernel
theorem tail17_40 : anyK (node 1 7) (k17.drop 40) = false := chainK _ _ 40 8 48 rfl part17_40 tail17_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part17_32 : anyK (node 1 7) ((k17.drop 32).take 8) = false := by decide +kernel
theorem tail17_32 : anyK (node 1 7) (k17.drop 32) = false := chainK _ _ 32 8 40 rfl part17_32 tail17_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part17_24 : anyK (node 1 7) ((k17.drop 24).take 8) = false := by decide +kernel
theorem tail17_24 : anyK (node 1 7) (k17.drop 24) = false := chainK _ _ 24 8 32 rfl part17_24 tail17_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part17_16 : anyK (node 1 7) ((k17.drop 16).take 8) = false := by decide +kernel
theorem tail17_16 : anyK (node 1 7) (k17.drop 16) = false := chainK _ _ 16 8 24 rfl part17_16 tail17_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part17_8 : anyK (node 1 7) ((k17.drop 8).take 8) = false := by decide +kernel
theorem tail17_8 : anyK (node 1 7) (k17.drop 8) = false := chainK _ _ 8 8 16 rfl part17_8 tail17_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part17_0 : anyK (node 1 7) ((k17.drop 0).take 8) = false := by decide +kernel
theorem tail17_0 : anyK (node 1 7) (k17.drop 0) = false := chainK _ _ 0 8 8 rfl part17_0 tail17_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_17 : anyK (node 1 8) ((kR.drop 17).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k17 tail17_0))
theorem qr_17 : anyK (node 1 8) (List.drop 17 kR) = false :=
  chainK (node 1 8) kR 17 1 18 rfl cr_17 qr_18
def k16 := kids (hdK (kR.drop 16)).1 (hdK (kR.drop 16)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail16_126 : anyK (node 1 7) (k16.drop 126) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_120 : anyK (node 1 7) ((k16.drop 120).take 6) = false := by decide +kernel
theorem tail16_120 : anyK (node 1 7) (k16.drop 120) = false := chainK _ _ 120 6 126 rfl part16_120 tail16_126
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_112 : anyK (node 1 7) ((k16.drop 112).take 8) = false := by decide +kernel
theorem tail16_112 : anyK (node 1 7) (k16.drop 112) = false := chainK _ _ 112 8 120 rfl part16_112 tail16_120
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_104 : anyK (node 1 7) ((k16.drop 104).take 8) = false := by decide +kernel
theorem tail16_104 : anyK (node 1 7) (k16.drop 104) = false := chainK _ _ 104 8 112 rfl part16_104 tail16_112
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_96 : anyK (node 1 7) ((k16.drop 96).take 8) = false := by decide +kernel
theorem tail16_96 : anyK (node 1 7) (k16.drop 96) = false := chainK _ _ 96 8 104 rfl part16_96 tail16_104
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_88 : anyK (node 1 7) ((k16.drop 88).take 8) = false := by decide +kernel
theorem tail16_88 : anyK (node 1 7) (k16.drop 88) = false := chainK _ _ 88 8 96 rfl part16_88 tail16_96
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_80 : anyK (node 1 7) ((k16.drop 80).take 8) = false := by decide +kernel
theorem tail16_80 : anyK (node 1 7) (k16.drop 80) = false := chainK _ _ 80 8 88 rfl part16_80 tail16_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_72 : anyK (node 1 7) ((k16.drop 72).take 8) = false := by decide +kernel
theorem tail16_72 : anyK (node 1 7) (k16.drop 72) = false := chainK _ _ 72 8 80 rfl part16_72 tail16_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_64 : anyK (node 1 7) ((k16.drop 64).take 8) = false := by decide +kernel
theorem tail16_64 : anyK (node 1 7) (k16.drop 64) = false := chainK _ _ 64 8 72 rfl part16_64 tail16_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_56 : anyK (node 1 7) ((k16.drop 56).take 8) = false := by decide +kernel
theorem tail16_56 : anyK (node 1 7) (k16.drop 56) = false := chainK _ _ 56 8 64 rfl part16_56 tail16_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_48 : anyK (node 1 7) ((k16.drop 48).take 8) = false := by decide +kernel
theorem tail16_48 : anyK (node 1 7) (k16.drop 48) = false := chainK _ _ 48 8 56 rfl part16_48 tail16_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_40 : anyK (node 1 7) ((k16.drop 40).take 8) = false := by decide +kernel
theorem tail16_40 : anyK (node 1 7) (k16.drop 40) = false := chainK _ _ 40 8 48 rfl part16_40 tail16_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_32 : anyK (node 1 7) ((k16.drop 32).take 8) = false := by decide +kernel
theorem tail16_32 : anyK (node 1 7) (k16.drop 32) = false := chainK _ _ 32 8 40 rfl part16_32 tail16_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_24 : anyK (node 1 7) ((k16.drop 24).take 8) = false := by decide +kernel
theorem tail16_24 : anyK (node 1 7) (k16.drop 24) = false := chainK _ _ 24 8 32 rfl part16_24 tail16_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_16 : anyK (node 1 7) ((k16.drop 16).take 8) = false := by decide +kernel
theorem tail16_16 : anyK (node 1 7) (k16.drop 16) = false := chainK _ _ 16 8 24 rfl part16_16 tail16_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_8 : anyK (node 1 7) ((k16.drop 8).take 8) = false := by decide +kernel
theorem tail16_8 : anyK (node 1 7) (k16.drop 8) = false := chainK _ _ 8 8 16 rfl part16_8 tail16_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part16_0 : anyK (node 1 7) ((k16.drop 0).take 8) = false := by decide +kernel
theorem tail16_0 : anyK (node 1 7) (k16.drop 0) = false := chainK _ _ 0 8 8 rfl part16_0 tail16_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_16 : anyK (node 1 8) ((kR.drop 16).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k16 tail16_0))
theorem qr_16 : anyK (node 1 8) (List.drop 16 kR) = false :=
  chainK (node 1 8) kR 16 1 17 rfl cr_16 qr_17
def k15 := kids (hdK (kR.drop 15)).1 (hdK (kR.drop 15)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail15_73 : anyK (node 1 7) (k15.drop 73) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part15_72 : anyK (node 1 7) ((k15.drop 72).take 1) = false := by decide +kernel
theorem tail15_72 : anyK (node 1 7) (k15.drop 72) = false := chainK _ _ 72 1 73 rfl part15_72 tail15_73
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part15_64 : anyK (node 1 7) ((k15.drop 64).take 8) = false := by decide +kernel
theorem tail15_64 : anyK (node 1 7) (k15.drop 64) = false := chainK _ _ 64 8 72 rfl part15_64 tail15_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part15_56 : anyK (node 1 7) ((k15.drop 56).take 8) = false := by decide +kernel
theorem tail15_56 : anyK (node 1 7) (k15.drop 56) = false := chainK _ _ 56 8 64 rfl part15_56 tail15_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part15_48 : anyK (node 1 7) ((k15.drop 48).take 8) = false := by decide +kernel
theorem tail15_48 : anyK (node 1 7) (k15.drop 48) = false := chainK _ _ 48 8 56 rfl part15_48 tail15_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part15_40 : anyK (node 1 7) ((k15.drop 40).take 8) = false := by decide +kernel
theorem tail15_40 : anyK (node 1 7) (k15.drop 40) = false := chainK _ _ 40 8 48 rfl part15_40 tail15_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part15_32 : anyK (node 1 7) ((k15.drop 32).take 8) = false := by decide +kernel
theorem tail15_32 : anyK (node 1 7) (k15.drop 32) = false := chainK _ _ 32 8 40 rfl part15_32 tail15_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part15_24 : anyK (node 1 7) ((k15.drop 24).take 8) = false := by decide +kernel
theorem tail15_24 : anyK (node 1 7) (k15.drop 24) = false := chainK _ _ 24 8 32 rfl part15_24 tail15_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part15_16 : anyK (node 1 7) ((k15.drop 16).take 8) = false := by decide +kernel
theorem tail15_16 : anyK (node 1 7) (k15.drop 16) = false := chainK _ _ 16 8 24 rfl part15_16 tail15_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part15_8 : anyK (node 1 7) ((k15.drop 8).take 8) = false := by decide +kernel
theorem tail15_8 : anyK (node 1 7) (k15.drop 8) = false := chainK _ _ 8 8 16 rfl part15_8 tail15_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part15_0 : anyK (node 1 7) ((k15.drop 0).take 8) = false := by decide +kernel
theorem tail15_0 : anyK (node 1 7) (k15.drop 0) = false := chainK _ _ 0 8 8 rfl part15_0 tail15_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_15 : anyK (node 1 8) ((kR.drop 15).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k15 tail15_0))
theorem qr_15 : anyK (node 1 8) (List.drop 15 kR) = false :=
  chainK (node 1 8) kR 15 1 16 rfl cr_15 qr_16
def k14 := kids (hdK (kR.drop 14)).1 (hdK (kR.drop 14)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail14_102 : anyK (node 1 7) (k14.drop 102) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part14_96 : anyK (node 1 7) ((k14.drop 96).take 6) = false := by decide +kernel
theorem tail14_96 : anyK (node 1 7) (k14.drop 96) = false := chainK _ _ 96 6 102 rfl part14_96 tail14_102
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part14_88 : anyK (node 1 7) ((k14.drop 88).take 8) = false := by decide +kernel
theorem tail14_88 : anyK (node 1 7) (k14.drop 88) = false := chainK _ _ 88 8 96 rfl part14_88 tail14_96
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part14_80 : anyK (node 1 7) ((k14.drop 80).take 8) = false := by decide +kernel
theorem tail14_80 : anyK (node 1 7) (k14.drop 80) = false := chainK _ _ 80 8 88 rfl part14_80 tail14_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part14_72 : anyK (node 1 7) ((k14.drop 72).take 8) = false := by decide +kernel
theorem tail14_72 : anyK (node 1 7) (k14.drop 72) = false := chainK _ _ 72 8 80 rfl part14_72 tail14_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part14_64 : anyK (node 1 7) ((k14.drop 64).take 8) = false := by decide +kernel
theorem tail14_64 : anyK (node 1 7) (k14.drop 64) = false := chainK _ _ 64 8 72 rfl part14_64 tail14_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part14_56 : anyK (node 1 7) ((k14.drop 56).take 8) = false := by decide +kernel
theorem tail14_56 : anyK (node 1 7) (k14.drop 56) = false := chainK _ _ 56 8 64 rfl part14_56 tail14_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part14_48 : anyK (node 1 7) ((k14.drop 48).take 8) = false := by decide +kernel
theorem tail14_48 : anyK (node 1 7) (k14.drop 48) = false := chainK _ _ 48 8 56 rfl part14_48 tail14_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part14_40 : anyK (node 1 7) ((k14.drop 40).take 8) = false := by decide +kernel
theorem tail14_40 : anyK (node 1 7) (k14.drop 40) = false := chainK _ _ 40 8 48 rfl part14_40 tail14_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part14_32 : anyK (node 1 7) ((k14.drop 32).take 8) = false := by decide +kernel
theorem tail14_32 : anyK (node 1 7) (k14.drop 32) = false := chainK _ _ 32 8 40 rfl part14_32 tail14_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part14_24 : anyK (node 1 7) ((k14.drop 24).take 8) = false := by decide +kernel
theorem tail14_24 : anyK (node 1 7) (k14.drop 24) = false := chainK _ _ 24 8 32 rfl part14_24 tail14_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part14_16 : anyK (node 1 7) ((k14.drop 16).take 8) = false := by decide +kernel
theorem tail14_16 : anyK (node 1 7) (k14.drop 16) = false := chainK _ _ 16 8 24 rfl part14_16 tail14_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part14_8 : anyK (node 1 7) ((k14.drop 8).take 8) = false := by decide +kernel
theorem tail14_8 : anyK (node 1 7) (k14.drop 8) = false := chainK _ _ 8 8 16 rfl part14_8 tail14_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part14_0 : anyK (node 1 7) ((k14.drop 0).take 8) = false := by decide +kernel
theorem tail14_0 : anyK (node 1 7) (k14.drop 0) = false := chainK _ _ 0 8 8 rfl part14_0 tail14_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_14 : anyK (node 1 8) ((kR.drop 14).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k14 tail14_0))
theorem qr_14 : anyK (node 1 8) (List.drop 14 kR) = false :=
  chainK (node 1 8) kR 14 1 15 rfl cr_14 qr_15
def k13 := kids (hdK (kR.drop 13)).1 (hdK (kR.drop 13)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail13_68 : anyK (node 1 7) (k13.drop 68) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part13_64 : anyK (node 1 7) ((k13.drop 64).take 4) = false := by decide +kernel
theorem tail13_64 : anyK (node 1 7) (k13.drop 64) = false := chainK _ _ 64 4 68 rfl part13_64 tail13_68
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part13_56 : anyK (node 1 7) ((k13.drop 56).take 8) = false := by decide +kernel
theorem tail13_56 : anyK (node 1 7) (k13.drop 56) = false := chainK _ _ 56 8 64 rfl part13_56 tail13_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part13_48 : anyK (node 1 7) ((k13.drop 48).take 8) = false := by decide +kernel
theorem tail13_48 : anyK (node 1 7) (k13.drop 48) = false := chainK _ _ 48 8 56 rfl part13_48 tail13_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part13_40 : anyK (node 1 7) ((k13.drop 40).take 8) = false := by decide +kernel
theorem tail13_40 : anyK (node 1 7) (k13.drop 40) = false := chainK _ _ 40 8 48 rfl part13_40 tail13_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part13_32 : anyK (node 1 7) ((k13.drop 32).take 8) = false := by decide +kernel
theorem tail13_32 : anyK (node 1 7) (k13.drop 32) = false := chainK _ _ 32 8 40 rfl part13_32 tail13_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part13_24 : anyK (node 1 7) ((k13.drop 24).take 8) = false := by decide +kernel
theorem tail13_24 : anyK (node 1 7) (k13.drop 24) = false := chainK _ _ 24 8 32 rfl part13_24 tail13_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part13_16 : anyK (node 1 7) ((k13.drop 16).take 8) = false := by decide +kernel
theorem tail13_16 : anyK (node 1 7) (k13.drop 16) = false := chainK _ _ 16 8 24 rfl part13_16 tail13_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part13_8 : anyK (node 1 7) ((k13.drop 8).take 8) = false := by decide +kernel
theorem tail13_8 : anyK (node 1 7) (k13.drop 8) = false := chainK _ _ 8 8 16 rfl part13_8 tail13_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part13_0 : anyK (node 1 7) ((k13.drop 0).take 8) = false := by decide +kernel
theorem tail13_0 : anyK (node 1 7) (k13.drop 0) = false := chainK _ _ 0 8 8 rfl part13_0 tail13_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_13 : anyK (node 1 8) ((kR.drop 13).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k13 tail13_0))
theorem qr_13 : anyK (node 1 8) (List.drop 13 kR) = false :=
  chainK (node 1 8) kR 13 1 14 rfl cr_13 qr_14
def k12 := kids (hdK (kR.drop 12)).1 (hdK (kR.drop 12)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail12_94 : anyK (node 1 7) (k12.drop 94) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part12_88 : anyK (node 1 7) ((k12.drop 88).take 6) = false := by decide +kernel
theorem tail12_88 : anyK (node 1 7) (k12.drop 88) = false := chainK _ _ 88 6 94 rfl part12_88 tail12_94
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part12_80 : anyK (node 1 7) ((k12.drop 80).take 8) = false := by decide +kernel
theorem tail12_80 : anyK (node 1 7) (k12.drop 80) = false := chainK _ _ 80 8 88 rfl part12_80 tail12_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part12_72 : anyK (node 1 7) ((k12.drop 72).take 8) = false := by decide +kernel
theorem tail12_72 : anyK (node 1 7) (k12.drop 72) = false := chainK _ _ 72 8 80 rfl part12_72 tail12_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part12_64 : anyK (node 1 7) ((k12.drop 64).take 8) = false := by decide +kernel
theorem tail12_64 : anyK (node 1 7) (k12.drop 64) = false := chainK _ _ 64 8 72 rfl part12_64 tail12_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part12_56 : anyK (node 1 7) ((k12.drop 56).take 8) = false := by decide +kernel
theorem tail12_56 : anyK (node 1 7) (k12.drop 56) = false := chainK _ _ 56 8 64 rfl part12_56 tail12_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part12_48 : anyK (node 1 7) ((k12.drop 48).take 8) = false := by decide +kernel
theorem tail12_48 : anyK (node 1 7) (k12.drop 48) = false := chainK _ _ 48 8 56 rfl part12_48 tail12_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part12_40 : anyK (node 1 7) ((k12.drop 40).take 8) = false := by decide +kernel
theorem tail12_40 : anyK (node 1 7) (k12.drop 40) = false := chainK _ _ 40 8 48 rfl part12_40 tail12_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part12_32 : anyK (node 1 7) ((k12.drop 32).take 8) = false := by decide +kernel
theorem tail12_32 : anyK (node 1 7) (k12.drop 32) = false := chainK _ _ 32 8 40 rfl part12_32 tail12_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part12_24 : anyK (node 1 7) ((k12.drop 24).take 8) = false := by decide +kernel
theorem tail12_24 : anyK (node 1 7) (k12.drop 24) = false := chainK _ _ 24 8 32 rfl part12_24 tail12_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part12_16 : anyK (node 1 7) ((k12.drop 16).take 8) = false := by decide +kernel
theorem tail12_16 : anyK (node 1 7) (k12.drop 16) = false := chainK _ _ 16 8 24 rfl part12_16 tail12_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part12_8 : anyK (node 1 7) ((k12.drop 8).take 8) = false := by decide +kernel
theorem tail12_8 : anyK (node 1 7) (k12.drop 8) = false := chainK _ _ 8 8 16 rfl part12_8 tail12_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part12_0 : anyK (node 1 7) ((k12.drop 0).take 8) = false := by decide +kernel
theorem tail12_0 : anyK (node 1 7) (k12.drop 0) = false := chainK _ _ 0 8 8 rfl part12_0 tail12_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_12 : anyK (node 1 8) ((kR.drop 12).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k12 tail12_0))
theorem qr_12 : anyK (node 1 8) (List.drop 12 kR) = false :=
  chainK (node 1 8) kR 12 1 13 rfl cr_12 qr_13
def k11 := kids (hdK (kR.drop 11)).1 (hdK (kR.drop 11)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail11_71 : anyK (node 1 7) (k11.drop 71) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part11_64 : anyK (node 1 7) ((k11.drop 64).take 7) = false := by decide +kernel
theorem tail11_64 : anyK (node 1 7) (k11.drop 64) = false := chainK _ _ 64 7 71 rfl part11_64 tail11_71
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part11_56 : anyK (node 1 7) ((k11.drop 56).take 8) = false := by decide +kernel
theorem tail11_56 : anyK (node 1 7) (k11.drop 56) = false := chainK _ _ 56 8 64 rfl part11_56 tail11_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part11_48 : anyK (node 1 7) ((k11.drop 48).take 8) = false := by decide +kernel
theorem tail11_48 : anyK (node 1 7) (k11.drop 48) = false := chainK _ _ 48 8 56 rfl part11_48 tail11_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part11_40 : anyK (node 1 7) ((k11.drop 40).take 8) = false := by decide +kernel
theorem tail11_40 : anyK (node 1 7) (k11.drop 40) = false := chainK _ _ 40 8 48 rfl part11_40 tail11_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part11_32 : anyK (node 1 7) ((k11.drop 32).take 8) = false := by decide +kernel
theorem tail11_32 : anyK (node 1 7) (k11.drop 32) = false := chainK _ _ 32 8 40 rfl part11_32 tail11_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part11_24 : anyK (node 1 7) ((k11.drop 24).take 8) = false := by decide +kernel
theorem tail11_24 : anyK (node 1 7) (k11.drop 24) = false := chainK _ _ 24 8 32 rfl part11_24 tail11_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part11_16 : anyK (node 1 7) ((k11.drop 16).take 8) = false := by decide +kernel
theorem tail11_16 : anyK (node 1 7) (k11.drop 16) = false := chainK _ _ 16 8 24 rfl part11_16 tail11_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part11_8 : anyK (node 1 7) ((k11.drop 8).take 8) = false := by decide +kernel
theorem tail11_8 : anyK (node 1 7) (k11.drop 8) = false := chainK _ _ 8 8 16 rfl part11_8 tail11_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part11_0 : anyK (node 1 7) ((k11.drop 0).take 8) = false := by decide +kernel
theorem tail11_0 : anyK (node 1 7) (k11.drop 0) = false := chainK _ _ 0 8 8 rfl part11_0 tail11_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_11 : anyK (node 1 8) ((kR.drop 11).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k11 tail11_0))
theorem qr_11 : anyK (node 1 8) (List.drop 11 kR) = false :=
  chainK (node 1 8) kR 11 1 12 rfl cr_11 qr_12
def k10 := kids (hdK (kR.drop 10)).1 (hdK (kR.drop 10)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail10_91 : anyK (node 1 7) (k10.drop 91) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part10_88 : anyK (node 1 7) ((k10.drop 88).take 3) = false := by decide +kernel
theorem tail10_88 : anyK (node 1 7) (k10.drop 88) = false := chainK _ _ 88 3 91 rfl part10_88 tail10_91
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part10_80 : anyK (node 1 7) ((k10.drop 80).take 8) = false := by decide +kernel
theorem tail10_80 : anyK (node 1 7) (k10.drop 80) = false := chainK _ _ 80 8 88 rfl part10_80 tail10_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part10_72 : anyK (node 1 7) ((k10.drop 72).take 8) = false := by decide +kernel
theorem tail10_72 : anyK (node 1 7) (k10.drop 72) = false := chainK _ _ 72 8 80 rfl part10_72 tail10_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part10_64 : anyK (node 1 7) ((k10.drop 64).take 8) = false := by decide +kernel
theorem tail10_64 : anyK (node 1 7) (k10.drop 64) = false := chainK _ _ 64 8 72 rfl part10_64 tail10_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part10_56 : anyK (node 1 7) ((k10.drop 56).take 8) = false := by decide +kernel
theorem tail10_56 : anyK (node 1 7) (k10.drop 56) = false := chainK _ _ 56 8 64 rfl part10_56 tail10_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part10_48 : anyK (node 1 7) ((k10.drop 48).take 8) = false := by decide +kernel
theorem tail10_48 : anyK (node 1 7) (k10.drop 48) = false := chainK _ _ 48 8 56 rfl part10_48 tail10_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part10_40 : anyK (node 1 7) ((k10.drop 40).take 8) = false := by decide +kernel
theorem tail10_40 : anyK (node 1 7) (k10.drop 40) = false := chainK _ _ 40 8 48 rfl part10_40 tail10_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part10_32 : anyK (node 1 7) ((k10.drop 32).take 8) = false := by decide +kernel
theorem tail10_32 : anyK (node 1 7) (k10.drop 32) = false := chainK _ _ 32 8 40 rfl part10_32 tail10_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part10_24 : anyK (node 1 7) ((k10.drop 24).take 8) = false := by decide +kernel
theorem tail10_24 : anyK (node 1 7) (k10.drop 24) = false := chainK _ _ 24 8 32 rfl part10_24 tail10_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part10_16 : anyK (node 1 7) ((k10.drop 16).take 8) = false := by decide +kernel
theorem tail10_16 : anyK (node 1 7) (k10.drop 16) = false := chainK _ _ 16 8 24 rfl part10_16 tail10_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part10_8 : anyK (node 1 7) ((k10.drop 8).take 8) = false := by decide +kernel
theorem tail10_8 : anyK (node 1 7) (k10.drop 8) = false := chainK _ _ 8 8 16 rfl part10_8 tail10_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part10_0 : anyK (node 1 7) ((k10.drop 0).take 8) = false := by decide +kernel
theorem tail10_0 : anyK (node 1 7) (k10.drop 0) = false := chainK _ _ 0 8 8 rfl part10_0 tail10_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_10 : anyK (node 1 8) ((kR.drop 10).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k10 tail10_0))
theorem qr_10 : anyK (node 1 8) (List.drop 10 kR) = false :=
  chainK (node 1 8) kR 10 1 11 rfl cr_10 qr_11
def k9 := kids (hdK (kR.drop 9)).1 (hdK (kR.drop 9)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail9_67 : anyK (node 1 7) (k9.drop 67) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part9_64 : anyK (node 1 7) ((k9.drop 64).take 3) = false := by decide +kernel
theorem tail9_64 : anyK (node 1 7) (k9.drop 64) = false := chainK _ _ 64 3 67 rfl part9_64 tail9_67
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part9_56 : anyK (node 1 7) ((k9.drop 56).take 8) = false := by decide +kernel
theorem tail9_56 : anyK (node 1 7) (k9.drop 56) = false := chainK _ _ 56 8 64 rfl part9_56 tail9_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part9_48 : anyK (node 1 7) ((k9.drop 48).take 8) = false := by decide +kernel
theorem tail9_48 : anyK (node 1 7) (k9.drop 48) = false := chainK _ _ 48 8 56 rfl part9_48 tail9_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part9_40 : anyK (node 1 7) ((k9.drop 40).take 8) = false := by decide +kernel
theorem tail9_40 : anyK (node 1 7) (k9.drop 40) = false := chainK _ _ 40 8 48 rfl part9_40 tail9_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part9_32 : anyK (node 1 7) ((k9.drop 32).take 8) = false := by decide +kernel
theorem tail9_32 : anyK (node 1 7) (k9.drop 32) = false := chainK _ _ 32 8 40 rfl part9_32 tail9_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part9_24 : anyK (node 1 7) ((k9.drop 24).take 8) = false := by decide +kernel
theorem tail9_24 : anyK (node 1 7) (k9.drop 24) = false := chainK _ _ 24 8 32 rfl part9_24 tail9_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part9_16 : anyK (node 1 7) ((k9.drop 16).take 8) = false := by decide +kernel
theorem tail9_16 : anyK (node 1 7) (k9.drop 16) = false := chainK _ _ 16 8 24 rfl part9_16 tail9_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part9_8 : anyK (node 1 7) ((k9.drop 8).take 8) = false := by decide +kernel
theorem tail9_8 : anyK (node 1 7) (k9.drop 8) = false := chainK _ _ 8 8 16 rfl part9_8 tail9_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part9_0 : anyK (node 1 7) ((k9.drop 0).take 8) = false := by decide +kernel
theorem tail9_0 : anyK (node 1 7) (k9.drop 0) = false := chainK _ _ 0 8 8 rfl part9_0 tail9_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_9 : anyK (node 1 8) ((kR.drop 9).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k9 tail9_0))
theorem qr_9 : anyK (node 1 8) (List.drop 9 kR) = false :=
  chainK (node 1 8) kR 9 1 10 rfl cr_9 qr_10
def k8 := kids (hdK (kR.drop 8)).1 (hdK (kR.drop 8)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail8_102 : anyK (node 1 7) (k8.drop 102) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part8_96 : anyK (node 1 7) ((k8.drop 96).take 6) = false := by decide +kernel
theorem tail8_96 : anyK (node 1 7) (k8.drop 96) = false := chainK _ _ 96 6 102 rfl part8_96 tail8_102
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part8_88 : anyK (node 1 7) ((k8.drop 88).take 8) = false := by decide +kernel
theorem tail8_88 : anyK (node 1 7) (k8.drop 88) = false := chainK _ _ 88 8 96 rfl part8_88 tail8_96
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part8_80 : anyK (node 1 7) ((k8.drop 80).take 8) = false := by decide +kernel
theorem tail8_80 : anyK (node 1 7) (k8.drop 80) = false := chainK _ _ 80 8 88 rfl part8_80 tail8_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part8_72 : anyK (node 1 7) ((k8.drop 72).take 8) = false := by decide +kernel
theorem tail8_72 : anyK (node 1 7) (k8.drop 72) = false := chainK _ _ 72 8 80 rfl part8_72 tail8_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part8_64 : anyK (node 1 7) ((k8.drop 64).take 8) = false := by decide +kernel
theorem tail8_64 : anyK (node 1 7) (k8.drop 64) = false := chainK _ _ 64 8 72 rfl part8_64 tail8_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part8_56 : anyK (node 1 7) ((k8.drop 56).take 8) = false := by decide +kernel
theorem tail8_56 : anyK (node 1 7) (k8.drop 56) = false := chainK _ _ 56 8 64 rfl part8_56 tail8_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part8_48 : anyK (node 1 7) ((k8.drop 48).take 8) = false := by decide +kernel
theorem tail8_48 : anyK (node 1 7) (k8.drop 48) = false := chainK _ _ 48 8 56 rfl part8_48 tail8_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part8_40 : anyK (node 1 7) ((k8.drop 40).take 8) = false := by decide +kernel
theorem tail8_40 : anyK (node 1 7) (k8.drop 40) = false := chainK _ _ 40 8 48 rfl part8_40 tail8_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part8_32 : anyK (node 1 7) ((k8.drop 32).take 8) = false := by decide +kernel
theorem tail8_32 : anyK (node 1 7) (k8.drop 32) = false := chainK _ _ 32 8 40 rfl part8_32 tail8_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part8_24 : anyK (node 1 7) ((k8.drop 24).take 8) = false := by decide +kernel
theorem tail8_24 : anyK (node 1 7) (k8.drop 24) = false := chainK _ _ 24 8 32 rfl part8_24 tail8_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part8_16 : anyK (node 1 7) ((k8.drop 16).take 8) = false := by decide +kernel
theorem tail8_16 : anyK (node 1 7) (k8.drop 16) = false := chainK _ _ 16 8 24 rfl part8_16 tail8_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part8_8 : anyK (node 1 7) ((k8.drop 8).take 8) = false := by decide +kernel
theorem tail8_8 : anyK (node 1 7) (k8.drop 8) = false := chainK _ _ 8 8 16 rfl part8_8 tail8_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part8_0 : anyK (node 1 7) ((k8.drop 0).take 8) = false := by decide +kernel
theorem tail8_0 : anyK (node 1 7) (k8.drop 0) = false := chainK _ _ 0 8 8 rfl part8_0 tail8_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_8 : anyK (node 1 8) ((kR.drop 8).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k8 tail8_0))
theorem qr_8 : anyK (node 1 8) (List.drop 8 kR) = false :=
  chainK (node 1 8) kR 8 1 9 rfl cr_8 qr_9
def k7 := kids (hdK (kR.drop 7)).1 (hdK (kR.drop 7)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail7_56 : anyK (node 1 7) (k7.drop 56) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part7_48 : anyK (node 1 7) ((k7.drop 48).take 8) = false := by decide +kernel
theorem tail7_48 : anyK (node 1 7) (k7.drop 48) = false := chainK _ _ 48 8 56 rfl part7_48 tail7_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part7_40 : anyK (node 1 7) ((k7.drop 40).take 8) = false := by decide +kernel
theorem tail7_40 : anyK (node 1 7) (k7.drop 40) = false := chainK _ _ 40 8 48 rfl part7_40 tail7_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part7_32 : anyK (node 1 7) ((k7.drop 32).take 8) = false := by decide +kernel
theorem tail7_32 : anyK (node 1 7) (k7.drop 32) = false := chainK _ _ 32 8 40 rfl part7_32 tail7_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part7_24 : anyK (node 1 7) ((k7.drop 24).take 8) = false := by decide +kernel
theorem tail7_24 : anyK (node 1 7) (k7.drop 24) = false := chainK _ _ 24 8 32 rfl part7_24 tail7_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part7_16 : anyK (node 1 7) ((k7.drop 16).take 8) = false := by decide +kernel
theorem tail7_16 : anyK (node 1 7) (k7.drop 16) = false := chainK _ _ 16 8 24 rfl part7_16 tail7_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part7_8 : anyK (node 1 7) ((k7.drop 8).take 8) = false := by decide +kernel
theorem tail7_8 : anyK (node 1 7) (k7.drop 8) = false := chainK _ _ 8 8 16 rfl part7_8 tail7_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part7_0 : anyK (node 1 7) ((k7.drop 0).take 8) = false := by decide +kernel
theorem tail7_0 : anyK (node 1 7) (k7.drop 0) = false := chainK _ _ 0 8 8 rfl part7_0 tail7_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_7 : anyK (node 1 8) ((kR.drop 7).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k7 tail7_0))
theorem qr_7 : anyK (node 1 8) (List.drop 7 kR) = false :=
  chainK (node 1 8) kR 7 1 8 rfl cr_7 qr_8
def k6 := kids (hdK (kR.drop 6)).1 (hdK (kR.drop 6)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail6_90 : anyK (node 1 7) (k6.drop 90) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part6_88 : anyK (node 1 7) ((k6.drop 88).take 2) = false := by decide +kernel
theorem tail6_88 : anyK (node 1 7) (k6.drop 88) = false := chainK _ _ 88 2 90 rfl part6_88 tail6_90
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part6_80 : anyK (node 1 7) ((k6.drop 80).take 8) = false := by decide +kernel
theorem tail6_80 : anyK (node 1 7) (k6.drop 80) = false := chainK _ _ 80 8 88 rfl part6_80 tail6_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part6_72 : anyK (node 1 7) ((k6.drop 72).take 8) = false := by decide +kernel
theorem tail6_72 : anyK (node 1 7) (k6.drop 72) = false := chainK _ _ 72 8 80 rfl part6_72 tail6_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part6_64 : anyK (node 1 7) ((k6.drop 64).take 8) = false := by decide +kernel
theorem tail6_64 : anyK (node 1 7) (k6.drop 64) = false := chainK _ _ 64 8 72 rfl part6_64 tail6_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part6_56 : anyK (node 1 7) ((k6.drop 56).take 8) = false := by decide +kernel
theorem tail6_56 : anyK (node 1 7) (k6.drop 56) = false := chainK _ _ 56 8 64 rfl part6_56 tail6_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part6_48 : anyK (node 1 7) ((k6.drop 48).take 8) = false := by decide +kernel
theorem tail6_48 : anyK (node 1 7) (k6.drop 48) = false := chainK _ _ 48 8 56 rfl part6_48 tail6_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part6_40 : anyK (node 1 7) ((k6.drop 40).take 8) = false := by decide +kernel
theorem tail6_40 : anyK (node 1 7) (k6.drop 40) = false := chainK _ _ 40 8 48 rfl part6_40 tail6_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part6_32 : anyK (node 1 7) ((k6.drop 32).take 8) = false := by decide +kernel
theorem tail6_32 : anyK (node 1 7) (k6.drop 32) = false := chainK _ _ 32 8 40 rfl part6_32 tail6_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part6_24 : anyK (node 1 7) ((k6.drop 24).take 8) = false := by decide +kernel
theorem tail6_24 : anyK (node 1 7) (k6.drop 24) = false := chainK _ _ 24 8 32 rfl part6_24 tail6_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part6_16 : anyK (node 1 7) ((k6.drop 16).take 8) = false := by decide +kernel
theorem tail6_16 : anyK (node 1 7) (k6.drop 16) = false := chainK _ _ 16 8 24 rfl part6_16 tail6_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part6_8 : anyK (node 1 7) ((k6.drop 8).take 8) = false := by decide +kernel
theorem tail6_8 : anyK (node 1 7) (k6.drop 8) = false := chainK _ _ 8 8 16 rfl part6_8 tail6_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part6_0 : anyK (node 1 7) ((k6.drop 0).take 8) = false := by decide +kernel
theorem tail6_0 : anyK (node 1 7) (k6.drop 0) = false := chainK _ _ 0 8 8 rfl part6_0 tail6_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_6 : anyK (node 1 8) ((kR.drop 6).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k6 tail6_0))
theorem qr_6 : anyK (node 1 8) (List.drop 6 kR) = false :=
  chainK (node 1 8) kR 6 1 7 rfl cr_6 qr_7
def k5 := kids (hdK (kR.drop 5)).1 (hdK (kR.drop 5)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail5_58 : anyK (node 1 7) (k5.drop 58) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part5_56 : anyK (node 1 7) ((k5.drop 56).take 2) = false := by decide +kernel
theorem tail5_56 : anyK (node 1 7) (k5.drop 56) = false := chainK _ _ 56 2 58 rfl part5_56 tail5_58
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part5_48 : anyK (node 1 7) ((k5.drop 48).take 8) = false := by decide +kernel
theorem tail5_48 : anyK (node 1 7) (k5.drop 48) = false := chainK _ _ 48 8 56 rfl part5_48 tail5_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part5_40 : anyK (node 1 7) ((k5.drop 40).take 8) = false := by decide +kernel
theorem tail5_40 : anyK (node 1 7) (k5.drop 40) = false := chainK _ _ 40 8 48 rfl part5_40 tail5_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part5_32 : anyK (node 1 7) ((k5.drop 32).take 8) = false := by decide +kernel
theorem tail5_32 : anyK (node 1 7) (k5.drop 32) = false := chainK _ _ 32 8 40 rfl part5_32 tail5_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part5_24 : anyK (node 1 7) ((k5.drop 24).take 8) = false := by decide +kernel
theorem tail5_24 : anyK (node 1 7) (k5.drop 24) = false := chainK _ _ 24 8 32 rfl part5_24 tail5_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part5_16 : anyK (node 1 7) ((k5.drop 16).take 8) = false := by decide +kernel
theorem tail5_16 : anyK (node 1 7) (k5.drop 16) = false := chainK _ _ 16 8 24 rfl part5_16 tail5_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part5_8 : anyK (node 1 7) ((k5.drop 8).take 8) = false := by decide +kernel
theorem tail5_8 : anyK (node 1 7) (k5.drop 8) = false := chainK _ _ 8 8 16 rfl part5_8 tail5_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part5_0 : anyK (node 1 7) ((k5.drop 0).take 8) = false := by decide +kernel
theorem tail5_0 : anyK (node 1 7) (k5.drop 0) = false := chainK _ _ 0 8 8 rfl part5_0 tail5_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_5 : anyK (node 1 8) ((kR.drop 5).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k5 tail5_0))
theorem qr_5 : anyK (node 1 8) (List.drop 5 kR) = false :=
  chainK (node 1 8) kR 5 1 6 rfl cr_5 qr_6
def k4 := kids (hdK (kR.drop 4)).1 (hdK (kR.drop 4)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail4_103 : anyK (node 1 7) (k4.drop 103) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part4_96 : anyK (node 1 7) ((k4.drop 96).take 7) = false := by decide +kernel
theorem tail4_96 : anyK (node 1 7) (k4.drop 96) = false := chainK _ _ 96 7 103 rfl part4_96 tail4_103
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part4_88 : anyK (node 1 7) ((k4.drop 88).take 8) = false := by decide +kernel
theorem tail4_88 : anyK (node 1 7) (k4.drop 88) = false := chainK _ _ 88 8 96 rfl part4_88 tail4_96
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part4_80 : anyK (node 1 7) ((k4.drop 80).take 8) = false := by decide +kernel
theorem tail4_80 : anyK (node 1 7) (k4.drop 80) = false := chainK _ _ 80 8 88 rfl part4_80 tail4_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part4_72 : anyK (node 1 7) ((k4.drop 72).take 8) = false := by decide +kernel
theorem tail4_72 : anyK (node 1 7) (k4.drop 72) = false := chainK _ _ 72 8 80 rfl part4_72 tail4_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part4_64 : anyK (node 1 7) ((k4.drop 64).take 8) = false := by decide +kernel
theorem tail4_64 : anyK (node 1 7) (k4.drop 64) = false := chainK _ _ 64 8 72 rfl part4_64 tail4_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part4_56 : anyK (node 1 7) ((k4.drop 56).take 8) = false := by decide +kernel
theorem tail4_56 : anyK (node 1 7) (k4.drop 56) = false := chainK _ _ 56 8 64 rfl part4_56 tail4_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part4_48 : anyK (node 1 7) ((k4.drop 48).take 8) = false := by decide +kernel
theorem tail4_48 : anyK (node 1 7) (k4.drop 48) = false := chainK _ _ 48 8 56 rfl part4_48 tail4_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part4_40 : anyK (node 1 7) ((k4.drop 40).take 8) = false := by decide +kernel
theorem tail4_40 : anyK (node 1 7) (k4.drop 40) = false := chainK _ _ 40 8 48 rfl part4_40 tail4_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part4_32 : anyK (node 1 7) ((k4.drop 32).take 8) = false := by decide +kernel
theorem tail4_32 : anyK (node 1 7) (k4.drop 32) = false := chainK _ _ 32 8 40 rfl part4_32 tail4_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part4_24 : anyK (node 1 7) ((k4.drop 24).take 8) = false := by decide +kernel
theorem tail4_24 : anyK (node 1 7) (k4.drop 24) = false := chainK _ _ 24 8 32 rfl part4_24 tail4_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part4_16 : anyK (node 1 7) ((k4.drop 16).take 8) = false := by decide +kernel
theorem tail4_16 : anyK (node 1 7) (k4.drop 16) = false := chainK _ _ 16 8 24 rfl part4_16 tail4_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part4_8 : anyK (node 1 7) ((k4.drop 8).take 8) = false := by decide +kernel
theorem tail4_8 : anyK (node 1 7) (k4.drop 8) = false := chainK _ _ 8 8 16 rfl part4_8 tail4_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part4_0 : anyK (node 1 7) ((k4.drop 0).take 8) = false := by decide +kernel
theorem tail4_0 : anyK (node 1 7) (k4.drop 0) = false := chainK _ _ 0 8 8 rfl part4_0 tail4_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_4 : anyK (node 1 8) ((kR.drop 4).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k4 tail4_0))
theorem qr_4 : anyK (node 1 8) (List.drop 4 kR) = false :=
  chainK (node 1 8) kR 4 1 5 rfl cr_4 qr_5
def k3 := kids (hdK (kR.drop 3)).1 (hdK (kR.drop 3)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail3_78 : anyK (node 1 7) (k3.drop 78) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part3_72 : anyK (node 1 7) ((k3.drop 72).take 6) = false := by decide +kernel
theorem tail3_72 : anyK (node 1 7) (k3.drop 72) = false := chainK _ _ 72 6 78 rfl part3_72 tail3_78
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part3_64 : anyK (node 1 7) ((k3.drop 64).take 8) = false := by decide +kernel
theorem tail3_64 : anyK (node 1 7) (k3.drop 64) = false := chainK _ _ 64 8 72 rfl part3_64 tail3_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part3_56 : anyK (node 1 7) ((k3.drop 56).take 8) = false := by decide +kernel
theorem tail3_56 : anyK (node 1 7) (k3.drop 56) = false := chainK _ _ 56 8 64 rfl part3_56 tail3_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part3_48 : anyK (node 1 7) ((k3.drop 48).take 8) = false := by decide +kernel
theorem tail3_48 : anyK (node 1 7) (k3.drop 48) = false := chainK _ _ 48 8 56 rfl part3_48 tail3_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part3_40 : anyK (node 1 7) ((k3.drop 40).take 8) = false := by decide +kernel
theorem tail3_40 : anyK (node 1 7) (k3.drop 40) = false := chainK _ _ 40 8 48 rfl part3_40 tail3_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part3_32 : anyK (node 1 7) ((k3.drop 32).take 8) = false := by decide +kernel
theorem tail3_32 : anyK (node 1 7) (k3.drop 32) = false := chainK _ _ 32 8 40 rfl part3_32 tail3_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part3_24 : anyK (node 1 7) ((k3.drop 24).take 8) = false := by decide +kernel
theorem tail3_24 : anyK (node 1 7) (k3.drop 24) = false := chainK _ _ 24 8 32 rfl part3_24 tail3_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part3_16 : anyK (node 1 7) ((k3.drop 16).take 8) = false := by decide +kernel
theorem tail3_16 : anyK (node 1 7) (k3.drop 16) = false := chainK _ _ 16 8 24 rfl part3_16 tail3_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part3_8 : anyK (node 1 7) ((k3.drop 8).take 8) = false := by decide +kernel
theorem tail3_8 : anyK (node 1 7) (k3.drop 8) = false := chainK _ _ 8 8 16 rfl part3_8 tail3_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part3_0 : anyK (node 1 7) ((k3.drop 0).take 8) = false := by decide +kernel
theorem tail3_0 : anyK (node 1 7) (k3.drop 0) = false := chainK _ _ 0 8 8 rfl part3_0 tail3_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_3 : anyK (node 1 8) ((kR.drop 3).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k3 tail3_0))
theorem qr_3 : anyK (node 1 8) (List.drop 3 kR) = false :=
  chainK (node 1 8) kR 3 1 4 rfl cr_3 qr_4
def k2 := kids (hdK (kR.drop 2)).1 (hdK (kR.drop 2)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail2_88 : anyK (node 1 7) (k2.drop 88) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part2_80 : anyK (node 1 7) ((k2.drop 80).take 8) = false := by decide +kernel
theorem tail2_80 : anyK (node 1 7) (k2.drop 80) = false := chainK _ _ 80 8 88 rfl part2_80 tail2_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part2_72 : anyK (node 1 7) ((k2.drop 72).take 8) = false := by decide +kernel
theorem tail2_72 : anyK (node 1 7) (k2.drop 72) = false := chainK _ _ 72 8 80 rfl part2_72 tail2_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part2_64 : anyK (node 1 7) ((k2.drop 64).take 8) = false := by decide +kernel
theorem tail2_64 : anyK (node 1 7) (k2.drop 64) = false := chainK _ _ 64 8 72 rfl part2_64 tail2_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part2_56 : anyK (node 1 7) ((k2.drop 56).take 8) = false := by decide +kernel
theorem tail2_56 : anyK (node 1 7) (k2.drop 56) = false := chainK _ _ 56 8 64 rfl part2_56 tail2_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part2_48 : anyK (node 1 7) ((k2.drop 48).take 8) = false := by decide +kernel
theorem tail2_48 : anyK (node 1 7) (k2.drop 48) = false := chainK _ _ 48 8 56 rfl part2_48 tail2_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part2_40 : anyK (node 1 7) ((k2.drop 40).take 8) = false := by decide +kernel
theorem tail2_40 : anyK (node 1 7) (k2.drop 40) = false := chainK _ _ 40 8 48 rfl part2_40 tail2_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part2_32 : anyK (node 1 7) ((k2.drop 32).take 8) = false := by decide +kernel
theorem tail2_32 : anyK (node 1 7) (k2.drop 32) = false := chainK _ _ 32 8 40 rfl part2_32 tail2_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part2_24 : anyK (node 1 7) ((k2.drop 24).take 8) = false := by decide +kernel
theorem tail2_24 : anyK (node 1 7) (k2.drop 24) = false := chainK _ _ 24 8 32 rfl part2_24 tail2_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part2_16 : anyK (node 1 7) ((k2.drop 16).take 8) = false := by decide +kernel
theorem tail2_16 : anyK (node 1 7) (k2.drop 16) = false := chainK _ _ 16 8 24 rfl part2_16 tail2_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part2_8 : anyK (node 1 7) ((k2.drop 8).take 8) = false := by decide +kernel
theorem tail2_8 : anyK (node 1 7) (k2.drop 8) = false := chainK _ _ 8 8 16 rfl part2_8 tail2_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part2_0 : anyK (node 1 7) ((k2.drop 0).take 8) = false := by decide +kernel
theorem tail2_0 : anyK (node 1 7) (k2.drop 0) = false := chainK _ _ 0 8 8 rfl part2_0 tail2_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_2 : anyK (node 1 8) ((kR.drop 2).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k2 tail2_0))
theorem qr_2 : anyK (node 1 8) (List.drop 2 kR) = false :=
  chainK (node 1 8) kR 2 1 3 rfl cr_2 qr_3
def k1 := kids (hdK (kR.drop 1)).1 (hdK (kR.drop 1)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail1_80 : anyK (node 1 7) (k1.drop 80) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part1_72 : anyK (node 1 7) ((k1.drop 72).take 8) = false := by decide +kernel
theorem tail1_72 : anyK (node 1 7) (k1.drop 72) = false := chainK _ _ 72 8 80 rfl part1_72 tail1_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part1_64 : anyK (node 1 7) ((k1.drop 64).take 8) = false := by decide +kernel
theorem tail1_64 : anyK (node 1 7) (k1.drop 64) = false := chainK _ _ 64 8 72 rfl part1_64 tail1_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part1_56 : anyK (node 1 7) ((k1.drop 56).take 8) = false := by decide +kernel
theorem tail1_56 : anyK (node 1 7) (k1.drop 56) = false := chainK _ _ 56 8 64 rfl part1_56 tail1_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part1_48 : anyK (node 1 7) ((k1.drop 48).take 8) = false := by decide +kernel
theorem tail1_48 : anyK (node 1 7) (k1.drop 48) = false := chainK _ _ 48 8 56 rfl part1_48 tail1_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part1_40 : anyK (node 1 7) ((k1.drop 40).take 8) = false := by decide +kernel
theorem tail1_40 : anyK (node 1 7) (k1.drop 40) = false := chainK _ _ 40 8 48 rfl part1_40 tail1_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part1_32 : anyK (node 1 7) ((k1.drop 32).take 8) = false := by decide +kernel
theorem tail1_32 : anyK (node 1 7) (k1.drop 32) = false := chainK _ _ 32 8 40 rfl part1_32 tail1_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part1_24 : anyK (node 1 7) ((k1.drop 24).take 8) = false := by decide +kernel
theorem tail1_24 : anyK (node 1 7) (k1.drop 24) = false := chainK _ _ 24 8 32 rfl part1_24 tail1_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part1_16 : anyK (node 1 7) ((k1.drop 16).take 8) = false := by decide +kernel
theorem tail1_16 : anyK (node 1 7) (k1.drop 16) = false := chainK _ _ 16 8 24 rfl part1_16 tail1_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part1_8 : anyK (node 1 7) ((k1.drop 8).take 8) = false := by decide +kernel
theorem tail1_8 : anyK (node 1 7) (k1.drop 8) = false := chainK _ _ 8 8 16 rfl part1_8 tail1_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part1_0 : anyK (node 1 7) ((k1.drop 0).take 8) = false := by decide +kernel
theorem tail1_0 : anyK (node 1 7) (k1.drop 0) = false := chainK _ _ 0 8 8 rfl part1_0 tail1_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_1 : anyK (node 1 8) ((kR.drop 1).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k1 tail1_0))
theorem qr_1 : anyK (node 1 8) (List.drop 1 kR) = false :=
  chainK (node 1 8) kR 1 1 2 rfl cr_1 qr_2
def k0 := kids (hdK (kR.drop 0)).1 (hdK (kR.drop 0)).2
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem tail0_121 : anyK (node 1 7) (k0.drop 121) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_120 : anyK (node 1 7) ((k0.drop 120).take 1) = false := by decide +kernel
theorem tail0_120 : anyK (node 1 7) (k0.drop 120) = false := chainK _ _ 120 1 121 rfl part0_120 tail0_121
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_112 : anyK (node 1 7) ((k0.drop 112).take 8) = false := by decide +kernel
theorem tail0_112 : anyK (node 1 7) (k0.drop 112) = false := chainK _ _ 112 8 120 rfl part0_112 tail0_120
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_104 : anyK (node 1 7) ((k0.drop 104).take 8) = false := by decide +kernel
theorem tail0_104 : anyK (node 1 7) (k0.drop 104) = false := chainK _ _ 104 8 112 rfl part0_104 tail0_112
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_96 : anyK (node 1 7) ((k0.drop 96).take 8) = false := by decide +kernel
theorem tail0_96 : anyK (node 1 7) (k0.drop 96) = false := chainK _ _ 96 8 104 rfl part0_96 tail0_104
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_88 : anyK (node 1 7) ((k0.drop 88).take 8) = false := by decide +kernel
theorem tail0_88 : anyK (node 1 7) (k0.drop 88) = false := chainK _ _ 88 8 96 rfl part0_88 tail0_96
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_80 : anyK (node 1 7) ((k0.drop 80).take 8) = false := by decide +kernel
theorem tail0_80 : anyK (node 1 7) (k0.drop 80) = false := chainK _ _ 80 8 88 rfl part0_80 tail0_88
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_72 : anyK (node 1 7) ((k0.drop 72).take 8) = false := by decide +kernel
theorem tail0_72 : anyK (node 1 7) (k0.drop 72) = false := chainK _ _ 72 8 80 rfl part0_72 tail0_80
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_64 : anyK (node 1 7) ((k0.drop 64).take 8) = false := by decide +kernel
theorem tail0_64 : anyK (node 1 7) (k0.drop 64) = false := chainK _ _ 64 8 72 rfl part0_64 tail0_72
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_56 : anyK (node 1 7) ((k0.drop 56).take 8) = false := by decide +kernel
theorem tail0_56 : anyK (node 1 7) (k0.drop 56) = false := chainK _ _ 56 8 64 rfl part0_56 tail0_64
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_48 : anyK (node 1 7) ((k0.drop 48).take 8) = false := by decide +kernel
theorem tail0_48 : anyK (node 1 7) (k0.drop 48) = false := chainK _ _ 48 8 56 rfl part0_48 tail0_56
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_40 : anyK (node 1 7) ((k0.drop 40).take 8) = false := by decide +kernel
theorem tail0_40 : anyK (node 1 7) (k0.drop 40) = false := chainK _ _ 40 8 48 rfl part0_40 tail0_48
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_32 : anyK (node 1 7) ((k0.drop 32).take 8) = false := by decide +kernel
theorem tail0_32 : anyK (node 1 7) (k0.drop 32) = false := chainK _ _ 32 8 40 rfl part0_32 tail0_40
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_24 : anyK (node 1 7) ((k0.drop 24).take 8) = false := by decide +kernel
theorem tail0_24 : anyK (node 1 7) (k0.drop 24) = false := chainK _ _ 24 8 32 rfl part0_24 tail0_32
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_16 : anyK (node 1 7) ((k0.drop 16).take 8) = false := by decide +kernel
theorem tail0_16 : anyK (node 1 7) (k0.drop 16) = false := chainK _ _ 16 8 24 rfl part0_16 tail0_24
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_8 : anyK (node 1 7) ((k0.drop 8).take 8) = false := by decide +kernel
theorem tail0_8 : anyK (node 1 7) (k0.drop 8) = false := chainK _ _ 8 8 16 rfl part0_8 tail0_16
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem part0_0 : anyK (node 1 7) ((k0.drop 0).take 8) = false := by decide +kernel
theorem tail0_0 : anyK (node 1 7) (k0.drop 0) = false := chainK _ _ 0 8 8 rfl part0_0 tail0_8
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cr_0 : anyK (node 1 8) ((kR.drop 0).take 1) = false := takeOneK _ _ (node_split 1 7 _ _ (by decide +kernel) (startK _ k0 tail0_0))
theorem qr_0 : anyK (node 1 8) (List.drop 0 kR) = false :=
  chainK (node 1 8) kR 0 1 1 rfl cr_0 qr_1
theorem pr : anyK (node 1 8) kR = false := startK _ _ qr_0

theorem root_goal : isGoal rowsN = false := by
  decide +kernel

theorem root_false : root 1 8 4 rowsN = false := root_split 1 8 4 rowsN root_goal pr

theorem reject : searchN 1 8 rowsN = false := by
  unfold searchN
  rw [List.any_eq_false]
  intro ws hws
  cases h : (decide (ws.length ≤ 8 + 2) && cutFull ws)
  · simp
  · have heq := only_full ws hws h
    subst heq
    have e : 8 + 2 - rowsN.length = 4 := by decide
    rw [e, root_false]
    simp

theorem goal_hi : goal.toNat = hiM := by
  decide +kernel

theorem goal_lo : (~~~goal).toNat = fullM := by
  decide +kernel

theorem sep_hi : Nat.land (sp hiM) fullM = fullM := by
  decide +kernel

theorem sep_lo : Nat.land (sp fullM) fullM = fullM := by
  decide +kernel

set_option maxRecDepth 8000 in
theorem bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : 9 < binaryCost gs :=
  bound_from_searchN rows rfl (by decide) (by rw [rows_eq]; exact reject) goal_hi goal_lo sep_hi sep_lo
    (by decide +kernel) gs o hg he

theorem bridge : ∀ x : Fin 6 → Bool, Nat.testBit (4276808426 * 2 ^ 32 + 4272482440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = F x := by
  intro x; rfl

def wg : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [4, 2]⟩, ⟨.and, [3, 6]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [4, 2]⟩, ⟨.or, [1, 9]⟩, ⟨.and, [8, 10]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [0, 13]⟩, ⟨.and, [12, 14]⟩, ⟨.or, [11, 15]⟩]

theorem wfits : PEqualNP.MetaComplexity.Monotone2 ⟨wg, 16⟩ := by
  intro g hg
  simp only [wg, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem weval : ∀ x : Fin 6 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wg, 16⟩ (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4272482440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end PEqualNP.Outside.L_meta_43470_aux

theorem PEqualNP.Outside.L_meta_43470 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808426 * 2 ^ 32 + 4272482440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808426 * 2 ^ 32 + 4272482440) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s ⟨C, hfan, hsize, heval⟩
  by_cases hasNot : ∃ g ∈ C.gates, g.op = PEqualNP.CircuitLowerBounds.GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : PEqualNP.Outside.L_meta_43470_aux.binaryCost C.gates < C.gates.length :=
      (List.length_filter_lt_length_iff_exists (p := PEqualNP.Outside.L_meta_43470_aux.isBinary)).mpr
        ⟨g, mem, by simp [PEqualNP.Outside.L_meta_43470_aux.isBinary, op]⟩
    have hleg : ∀ g ∈ C.gates, PEqualNP.Outside.L_meta_43470_aux.legal g := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hfan g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
      exact ⟨hop, hlen⟩
    have hb := PEqualNP.Outside.L_meta_43470_aux.bound C.gates C.output hleg (fun x => (heval x).trans (PEqualNP.Outside.L_meta_43470_aux.bridge x))
    have hsz : C.size = C.gates.length := rfl
    have hl : (⟨PEqualNP.Outside.L_meta_43470_aux.wg, 16⟩ : PEqualNP.CircuitLowerBounds.Circuit).size = 11 := rfl
    exact ⟨⟨PEqualNP.Outside.L_meta_43470_aux.wg, 16⟩, PEqualNP.Outside.L_meta_43470_aux.wfits, by omega, PEqualNP.Outside.L_meta_43470_aux.weval⟩
  · refine ⟨C, ?_, hsize, heval⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hasNot ⟨g, hg, h⟩).elim
