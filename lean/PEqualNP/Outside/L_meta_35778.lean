import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_35778

def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)

def decodeNode (parentWidth width packed index : Nat) : Nat × Nat :=
  let entry := unpack packed width index
  (entry &&& ((1 <<< parentWidth) - 1), entry >>> parentWidth)

def treeBlock (start count : Nat) (check : Nat → Bool) : Bool :=
  (Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ next i => check i && next (i + 1)) count) start

theorem treeBlock_at {start count i : Nat} {check : Nat → Bool}
    (h : treeBlock start count check = true) (lo : start ≤ i) (hi : i < start + count) :
    check i = true := by
  induction count generalizing start with
  | zero => omega
  | succ count ih =>
    change (check start && treeBlock (start + 1) count check) = true at h
    rcases Bool.and_eq_true_iff.mp h with ⟨here, rest⟩
    by_cases eq : i = start
    · simpa [eq] using here
    · exact ih rest (by omega) (by omega)

theorem treeBlock_merge {start left right : Nat} {check : Nat → Bool}
    (a : treeBlock start left check = true)
    (b : treeBlock (start + left) right check = true) :
    treeBlock start (left + right) check = true := by
  induction left generalizing start with
  | zero => simpa using b
  | succ left ih =>
    rw [Nat.succ_add]
    change (check start && treeBlock (start + 1) (left + right) check) = true
    change (check start && treeBlock (start + 1) left check) = true at a
    rcases Bool.and_eq_true_iff.mp a with ⟨here, rest⟩
    exact Bool.and_eq_true_iff.mpr ⟨here, ih rest (by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b)⟩

def rootWords (base : List Nat) (token : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun word _ next bits =>
      let tail := next (bits >>> 1)
      if bits &&& 1 == 0 then tail else word :: tail) base token

def rootState (base : List Nat) (fuel token : Nat) : (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (fuel, rootWords base token, [])

def insertWord (w : Nat) (ws : List Nat) : List Nat :=
  List.rec [w] (fun a tail next => if w ≤ a then w :: a :: tail else a :: next) ws

def childState (mask token : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, history) := state
  let keep := token % 4
  let op := (token / 4) % 3
  let a := token / (4 * 3 * 64)
  let b := (token / (4 * 3)) % 64
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else
    let x := ws.getD a 0
    let y := ws.getD b 0
    let w := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
    if w == 0 || w == mask || ws.contains w then none
    else
      let rest := if keep.testBit 0 then ws else ws.erase x
      let rest := if op == 2 || keep.testBit 1 then rest else rest.erase y
      some (fuel - 1, insertWord w rest, (w, x, y) :: history)

def gateToken (a b op keep : Nat) : Nat := ((a * 64 + b) * 3 + op) * 4 + keep

def stockWord (mask : Nat) (stock : List Nat) (needed : List Nat) (word : Nat) : List Nat :=
  let v := word &&& mask
  if v == 0 || v == mask || stock.contains v || needed.contains v then needed
  else v :: needed

def recipeStart (mask : Nat) (stock words : List Nat) : List Nat :=
  (List.rec (motive := fun _ => List Nat → List Nat) id
    (fun word _ next seen => next (stockWord mask stock seen word)) words) []

def recipeClosure (mask : Nat) (stock : List Nat) (history : List (Nat × Nat × Nat))
    (start : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) id
    (fun (out, a, b) _ next seen =>
      next (if seen.contains (out &&& mask) then stockWord mask stock (stockWord mask stock seen a) b else seen))
    history start

def recipeNeeded (mask : Nat) (stock words : List Nat) (history : List (Nat × Nat × Nat)) :
    List Nat :=
  recipeClosure mask stock history (recipeStart mask stock words)

def maskFlat (mask word : Nat) : Bool :=
  let v := word &&& mask
  v == 0 || v == mask

def flatCount (mask : Nat) (words : List Nat) : Nat :=
  List.rec 0 (fun word _ count => if maskFlat mask word then count + 1 else count) words

def availableB (mask : Nat) (bank : List Nat) (w : Nat) : Bool :=
  w == 0 || w == mask || bank.contains w

def recipeGate (mask : Nat) (bank : List Nat) (w a b : Nat) : Bool :=
  availableB mask bank a &&
    ((w == mask ^^^ a) || (availableB mask bank b && (w == a &&& b || w == a ||| b)))

def replayRecipes (mask : Nat) (needed : List Nat) (recipes : List (Nat × Nat × Nat))
    (bank : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun (w, a, b) _ next bank =>
      let v := w &&& mask
      if needed.contains v && !availableB mask bank v &&
          recipeGate mask bank v (a &&& mask) (b &&& mask) then
        v :: next (v :: bank)
      else next bank) recipes bank

def boundCloses (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (bound : (Nat × List Nat × Nat × Nat)) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    (let remaining := fuel - flatCount mask ws
     if remaining < lower then
       let start := recipeStart mask stock ws
       if start.length + remaining < lower then
         let needed := recipeClosure mask stock history start
         if needed.length + remaining < lower then
           let replay := replayRecipes mask needed history.reverse stock
           (replay.length + remaining < lower) &&
             ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask))
         else false
       else false
     else false)

def knownCloses (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  List.rec false (fun bound _ later => boundCloses target state bound || later) bounds

def AvailableWord (mask : Nat) (bank : List Nat) (word : Nat) : Prop :=
  word = 0 ∨ word = mask ∨ word ∈ bank

def GateWord (mask : Nat) (bank : List Nat) (out : Nat) : Prop :=
  (∃ a, AvailableWord mask bank a ∧ out = mask ^^^ a) ∨
  (∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b))

def WordBuilds (mask : Nat) (roots : List Nat) : List Nat → Prop
  | [] => True
  | w :: ws => GateWord mask roots w ∧ WordBuilds mask (w :: roots) ws

def Lower (mask : Nat) (roots : List Nat) (target : Nat) (minimum : Nat) : Prop :=
  ∀ values, WordBuilds mask roots values →
    AvailableWord mask (values ++ roots) target → minimum ≤ values.length

def Known (bounds : List (Nat × List Nat × Nat × Nat)) : Prop :=
  ∀ bound ∈ bounds, Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1

theorem restrictWord (mask : Nat) (word : Nat) : word &&& mask &&& mask = word &&& mask := by
  simp

theorem projectGate {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots : List Nat} {out : Nat} (gate : GateWord mask roots out) :
    GateWord cut (roots.map (· &&& cut)) (out &&& cut) := by
  have av {word : Nat} (ha : AvailableWord mask roots word) :
      AvailableWord cut (roots.map (· &&& cut)) (word &&& cut) := by
    rcases ha with rfl | rfl | hm
    · exact Or.inl (by simp)
    · exact Or.inr (Or.inl submask)
    · exact Or.inr (Or.inr (List.mem_map_of_mem hm))
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · refine Or.inl ⟨a &&& cut, av ha, ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    have cutAt := congrArg (fun n : Nat => n.testBit i) submask
    simp only [Nat.testBit_and, Nat.testBit_xor] at cutAt ⊢
    cases h : cut.testBit i
    · simp
    · simp [h] at cutAt
      simp [cutAt]
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inl ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and]
    cases cut.testBit i <;> simp
  · subst out
    refine Or.inr ⟨a &&& cut, b &&& cut, av ha, av hb, Or.inr ?_⟩
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases cut.testBit i <;> simp

theorem projectBuilds {mask cut : Nat} (submask : mask &&& cut = cut)
    {roots values : List Nat} (builds : WordBuilds mask roots values) :
    WordBuilds cut (roots.map (· &&& cut)) (values.map (· &&& cut)) := by
  induction values generalizing roots with
  | nil => trivial
  | cons w ws ih =>
    exact ⟨projectGate submask builds.1, ih builds.2⟩

theorem availableWeaken {mask : Nat} {small big : List Nat} {w : Nat}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (av : AvailableWord mask small w) : AvailableWord mask big w := by
  rcases av with rfl | rfl | h
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact sub w h

theorem gateWeaken {mask : Nat} {small big : List Nat} {out : Nat}
    (sub : ∀ x ∈ small, AvailableWord mask big x)
    (gate : GateWord mask small out) : GateWord mask big out := by
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq⟩
  · exact Or.inl ⟨a, availableWeaken sub ha, rfl⟩
  · exact Or.inr ⟨a, b, availableWeaken sub ha, availableWeaken sub hb, eq⟩

theorem extendKnown {bound : (Nat × List Nat × Nat × Nat)} {bounds : List (Nat × List Nat × Nat × Nat)}
    (old : Known bounds)
    (new : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1) :
    Known (bound :: bounds) := by
  intro x h
  rcases List.mem_cons.mp h with rfl | h
  · exact new
  · exact old _ h

def AgreesAt (i j : Nat) (word : Nat) : Prop :=
  word.testBit i = word.testBit j

theorem agreesAvailable {i j mask : Nat} {bank : List Nat} {word : Nat}
    (m : AgreesAt i j mask) (all : ∀ w ∈ bank, AgreesAt i j w)
    (av : AvailableWord mask bank word) : AgreesAt i j word := by
  rcases av with rfl | rfl | h
  · simp [AgreesAt]
  · exact m
  · exact all _ h

theorem agreesGate {i j mask : Nat} {bank : List Nat} {word : Nat}
    (m : AgreesAt i j mask) (all : ∀ w ∈ bank, AgreesAt i j w)
    (gate : GateWord mask bank word) : AgreesAt i j word := by
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, eq | eq⟩
  · simp only [AgreesAt, Nat.testBit_xor] at m ⊢
    rw [m, show a.testBit i = a.testBit j from agreesAvailable m all ha]
  · subst word
    simp only [AgreesAt, Nat.testBit_and]
    rw [show a.testBit i = a.testBit j from agreesAvailable m all ha,
      show b.testBit i = b.testBit j from agreesAvailable m all hb]
  · subst word
    simp only [AgreesAt, Nat.testBit_or]
    rw [show a.testBit i = a.testBit j from agreesAvailable m all ha,
      show b.testBit i = b.testBit j from agreesAvailable m all hb]

theorem agreesBuilds {i j mask : Nat} {roots values : List Nat} {word : Nat}
    (m : AgreesAt i j mask) (all : ∀ w ∈ roots, AgreesAt i j w)
    (builds : WordBuilds mask roots values)
    (av : AvailableWord mask (values ++ roots) word) : AgreesAt i j word := by
  induction values generalizing roots with
  | nil => exact agreesAvailable m all av
  | cons v vs ih =>
    have vg := agreesGate m all builds.1
    have hc : ∀ w ∈ v :: roots, AgreesAt i j w := by
      intro w h
      rcases List.mem_cons.mp h with rfl | mem
      · exact vg
      · exact all _ mem
    apply ih hc builds.2
    rcases av with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by
        simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using h))

theorem buildsMap {m n : Nat} (f : Nat → Nat)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots : List Nat} {bank : List Nat}
    (supply : ∀ v ∈ roots, AvailableWord n bank (f v))
    {values : List Nat} (h : WordBuilds m roots values) :
    WordBuilds n bank (values.map f) := by
  have av {bank roots : List Nat} {v : Nat}
      (src : ∀ v ∈ roots, AvailableWord n bank (f v))
      (h : AvailableWord m roots v) : AvailableWord n bank (f v) := by
    rcases h with rfl | rfl | hv
    · exact Or.inl zero
    · exact Or.inr (Or.inl ones)
    · exact src _ hv
  induction values generalizing roots bank with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨?_, ih ?_ h.2⟩
    · rcases h.1 with ⟨a, ha, eq⟩ | ⟨a, b, ha, hb, eq | eq⟩
      · exact Or.inl ⟨f a, av supply ha, eq ▸ invert a⟩
      · exact Or.inr ⟨f a, f b, av supply ha, av supply hb, Or.inl (eq ▸ meet a b)⟩
      · exact Or.inr ⟨f a, f b, av supply ha, av supply hb, Or.inr (eq ▸ join a b)⟩
    · intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inr (Or.inr List.mem_cons_self)
      · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem lowerMap {m n : Nat} (f : Nat → Nat)
    (zero : f 0 = 0) (ones : f m = n)
    (invert : ∀ a, f (m ^^^ a) = n ^^^ f a)
    (meet : ∀ a b, f (a &&& b) = f a &&& f b)
    (join : ∀ a b, f (a ||| b) = f a ||| f b)
    {roots bank : List Nat} {goal : Nat} {minimum : Nat}
    (supply : ∀ v ∈ roots, AvailableWord n bank (f v))
    (bound : Lower n bank (f goal) minimum) :
    Lower m roots goal minimum := by
  intro values build hit
  suffices AvailableWord n (values.map f ++ bank) (f goal) by
    simpa using bound (values.map f) (buildsMap f zero ones invert meet join supply build) this
  rcases hit with rfl | rfl | mem
  · exact Or.inl zero
  · exact Or.inr (Or.inl ones)
  · rcases List.mem_append.mp mem with hv | hr
    · exact Or.inr (Or.inr (List.mem_append_left _ (List.mem_map_of_mem hv)))
    · exact availableWeaken (fun w hw => Or.inr (Or.inr (List.mem_append_right _ hw))) (supply _ hr)

theorem buildsWeaken {mask : Nat} {small big values : List Nat}
    (supply : ∀ w ∈ small, AvailableWord mask big w) (build : WordBuilds mask small values) :
    WordBuilds mask big values := by
  induction values generalizing small big with
  | nil => trivial
  | cons v vs ih =>
    refine ⟨gateWeaken supply build.1, ih ?_ build.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inr (Or.inr List.mem_cons_self)
    · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem gateBuildsIndex {mask : Nat} (bank values : List Nat)
    (legal : ∀ i, i < values.length →
      GateWord mask (bank ++ values.take i) (values.getD i 0)) :
    WordBuilds mask bank values := by
  induction values generalizing bank with
  | nil => trivial
  | cons v vs ih =>
    have first := legal 0 (by simp)
    have tail : ∀ i, i < vs.length →
        GateWord mask ((bank ++ [v]) ++ vs.take i) (vs.getD i 0) := by
      intro i hi
      simpa [List.take_succ_cons, List.append_assoc] using
        legal (i + 1) (by simpa using hi)
    refine ⟨by simpa using first, buildsWeaken ?_ (ih (bank ++ [v]) tail)⟩
    intro w mem
    exact Or.inr (Or.inr (by simpa [or_comm] using mem))

theorem lowerWeaken {mask goal minimum : Nat} {old new : List Nat}
    (lower : Lower mask old goal minimum) (supply : ∀ w ∈ new, AvailableWord mask old w) :
    Lower mask new goal minimum := by
  apply lowerMap id rfl rfl (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) supply
  exact lower

def properWord (mask word : Nat) : Prop := word ≠ 0 ∧ word ≠ mask

def binWord (isOr : Bool) (a b : Nat) : Nat :=
  if isOr then a ||| b else a &&& b

theorem binWord_comm (d : Bool) (a b : Nat) : binWord d a b = binWord d b a := by
  cases d <;> simp [binWord, Nat.land_comm, Nat.lor_comm]

variable {mask : Nat} {target : Nat}

def LiveWord (mask : Nat) (target : Nat) : Nat → Nat → Finset (Nat) → Prop
  | 0,t,S => t=0 ∧ S={target} ∧ properWord mask target
  | k+1,t,S =>
    (∃ (u : Nat) (U : Finset (Nat)) (a : Nat), t=u+1 ∧ S=insert a U ∧ properWord mask a ∧
      (mask ^^^ a) ∉ insert a U ∧ LiveWord mask target k u (insert ((mask ^^^ a)) U)) ∨
    (∃ (U : Finset (Nat)) (a b : Nat) (d : Bool), S=insert a (insert b U) ∧ properWord mask a ∧ properWord mask b ∧ a ≠ b ∧
      binWord d a b ∉ insert a (insert b U) ∧ LiveWord mask target k t (insert (binWord d a b) U))
theorem LiveWord.stop {target : Nat} (hp : properWord mask target) : LiveWord mask target 0 0 {target} := ⟨rfl,rfl,hp⟩
theorem LiveWord.unary {target : Nat} {k t : Nat} {U : Finset (Nat)} {a : Nat} (ha : properWord mask a)
    (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)) :
    LiveWord mask target (k+1) (t+1) (insert a U) :=
  Or.inl ⟨t,U,a,rfl,rfl,ha,hfresh,tail⟩
theorem LiveWord.binary {target : Nat} {k t : Nat} {U : Finset (Nat)} {a b : Nat} {d : Bool}
    (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
    (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)) :
    LiveWord mask target (k+1) t (insert a (insert b U)) :=
  Or.inr ⟨U,a,b,d,rfl,ha,hb,hab,hfresh,tail⟩
theorem LiveWord.ind {target : Nat} {motive : ∀ (k t : Nat) (S : Finset (Nat)), LiveWord mask target k t S → Prop}
    (stop : ∀ (hp : properWord mask target), motive 0 0 {target} (LiveWord.stop hp))
    (unary : ∀ {k t : Nat} {U : Finset (Nat)} {a : Nat} (ha : properWord mask a)
      (hfresh : (mask ^^^ a) ∉ insert a U) (tail : LiveWord mask target k t (insert ((mask ^^^ a)) U)),
      motive k t (insert ((mask ^^^ a)) U) tail → motive (k+1) (t+1) (insert a U) (LiveWord.unary ha hfresh tail))
    (binary : ∀ {k t : Nat} {U : Finset (Nat)} {a b : Nat} {d : Bool}
      (ha : properWord mask a) (hb : properWord mask b) (hab : a ≠ b)
      (hfresh : binWord d a b ∉ insert a (insert b U)) (tail : LiveWord mask target k t (insert (binWord d a b) U)),
      motive k t (insert (binWord d a b) U) tail →
      motive (k+1) t (insert a (insert b U)) (LiveWord.binary ha hb hab hfresh tail))
    {k t : Nat} {S : Finset (Nat)} (h : LiveWord mask target k t S) : motive k t S h := by
  induction k generalizing t S with
  | zero =>
    obtain ⟨rfl,rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    rcases h with ⟨u,U,a,rfl,rfl,ha,hf,tail⟩ | ⟨U,a,b,d,rfl,ha,hb,hab,hf,tail⟩
    · exact unary ha hf tail (ih tail)
    · exact binary ha hb hab hf tail (ih tail)

theorem liveWordProper {k t S} (h : LiveWord mask target k t S) : ∀ a ∈ S, properWord mask a := by
  induction h using LiveWord.ind with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

theorem liveWordSize {k t S} (h : LiveWord mask target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h using LiveWord.ind with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : (mask ^^^ a) ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : binWord d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩

def wordRep (mask : Nat) (ws : List Nat) (w : Nat) : Prop :=
  w ∈ ws ∨ ¬properWord mask w

def wordWitness (mask : Nat) (ws : List Nat) (w : Nat) : Prop :=
  (∃ a ∈ ws, properWord mask a ∧ w = mask ^^^ a) ∨
  ∃ d a b, a ∈ ws ∧ b ∈ ws ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ w = binWord d a b

theorem pullWord {w : List (Nat)} {z : Nat} {k t S} (h : LiveWord mask target k t S)
    (hz : wordRep mask w z ∨ wordWitness mask w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ LiveWord mask target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := liveWordProper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase ((mask ^^^ a))
        have ht : LiveWord mask target k t (insert ((mask ^^^ a)) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : (mask ^^^ a) ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,LiveWord.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (binWord d a b)
        have ht : LiveWord mask target k t (insert (binWord d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : binWord d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,LiveWord.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha



def Masked (mask word : Nat) : Prop := word &&& mask = word

theorem maskedAvailable {bank : List Nat} {word : Nat}
    (all : ∀ w ∈ bank, Masked mask w) (aw : AvailableWord mask bank word) :
    Masked mask word := by
  rcases aw with rfl | rfl | hw
  · simp [Masked]
  · simp [Masked]
  · exact all _ hw

theorem maskedGate {bank : List Nat} {out : Nat}
    (all : ∀ w ∈ bank, Masked mask w) (g : GateWord mask bank out) :
    Masked mask out := by
  rcases g with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, ea | ea⟩
  · have h := projectGate (mask := mask) (cut := mask) (by simp)
      (roots := bank) (out := mask ^^^ a) (Or.inl ⟨a, ha, rfl⟩)
    have ma := maskedAvailable all ha
    unfold Masked at ma ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bit := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_xor] at bit ⊢
    cases hm : mask.testBit i <;> simp_all
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    simp only [Masked] at ma mb ⊢
    rw [Nat.land_assoc, mb]
  · subst out
    have ma := maskedAvailable all ha
    have mb := maskedAvailable all hb
    unfold Masked at ma mb ⊢
    apply Nat.eq_of_testBit_eq
    intro i
    have bitA := congrArg (fun n : Nat => n.testBit i) ma
    have bitB := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at bitA bitB ⊢
    cases hm : mask.testBit i <;> simp_all

def binaryWitness (mask : Nat) (bank : List Nat) (out : Nat) : Prop :=
  ∃ d a b, a ∈ bank ∧ b ∈ bank ∧ properWord mask a ∧ properWord mask b ∧
    a ≠ b ∧ out = binWord d a b

theorem classifyBinary {bank : List Nat}
    (all : ∀ w ∈ bank, Masked mask w) (d : Bool) {a b : Nat}
    (ha : AvailableWord mask bank a) (hb : AvailableWord mask bank b) :
    wordRep mask bank (binWord d a b) ∨ binaryWitness mask bank (binWord d a b) := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Nat} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  have ma : a &&& mask = a := maskedAvailable all ha
  have mb : b &&& mask = b := maskedAvailable all hb
  have absorbA : a ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) ma
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  have absorbB : b ||| mask = mask := by
    apply Nat.eq_of_testBit_eq
    intro i
    have h := congrArg (fun n : Nat => n.testBit i) mb
    simp only [Nat.testBit_and, Nat.testBit_or] at h ⊢
    cases hm : mask.testBit i <;> simp_all
  rcases classify ha with rfl | hma | ⟨ha', pa⟩
  · rw [binWord_comm]
    cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, wordRep] using
          (Or.inl hv : wordRep mask bank b))
  · rw [hma, binWord_comm]
    cases d
    · rcases hb with hz | hm | hv
      · exact Or.inl (by simpa [binWord, hz] using c0)
      · exact Or.inl (by simpa [binWord, hm] using cm)
      · exact Or.inl (by simpa [binWord, mb, wordRep] using
          (Or.inl hv : wordRep mask bank b))
    · exact Or.inl (by simpa [binWord, absorbB] using cm)
  rcases classify hb with rfl | hmb | ⟨hb', pb⟩
  · cases d
    · exact Or.inl (by simpa [binWord] using c0)
    · exact Or.inl (by simpa [binWord, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
  · rw [hmb]
    cases d
    · exact Or.inl (by simpa [binWord, ma, wordRep] using
        (Or.inl ha' : wordRep mask bank a))
    · exact Or.inl (by simpa [binWord, absorbA] using cm)
  by_cases eq : a = b
  · subst b
    cases d <;> exact Or.inl (by simpa [binWord, wordRep] using
      (Or.inl ha' : wordRep mask bank a))
  exact Or.inr ⟨d, a, b, ha', hb', pa, pb, eq, rfl⟩

theorem classifyWord {bank : List Nat} {out : Nat}
    (all : ∀ w ∈ bank, Masked mask w) (gate : GateWord mask bank out) :
    wordRep mask bank out ∨ wordWitness mask bank out := by
  have c0 : wordRep mask bank 0 := Or.inr fun h => h.1 rfl
  have cm : wordRep mask bank mask := Or.inr fun h => h.2 rfl
  have classify {w : Nat} (hw : AvailableWord mask bank w) :
      w = 0 ∨ w = mask ∨ w ∈ bank ∧ properWord mask w := by
    by_cases zh : w = 0
    · exact Or.inl zh
    by_cases mh : w = mask
    · exact Or.inr (Or.inl mh)
    exact Or.inr (Or.inr ⟨(hw.resolve_left zh).resolve_left mh, zh, mh⟩)
  rcases gate with ⟨a, ha, rfl⟩ | ⟨a, b, ha, hb, h | h⟩
  · rcases classify ha with rfl | hma | ⟨hm, hp⟩
    · exact Or.inl (by simpa using cm)
    · exact Or.inl (by simpa [hma] using c0)
    · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
  · subst out; exact (classifyBinary all false ha hb).imp id Or.inr
  · subst out; exact (classifyBinary all true ha hb).imp id Or.inr

theorem extractWordLive {roots values : List Nat}
    (all : ∀ w ∈ roots, Masked mask w) (builds : WordBuilds mask roots values)
    (hit : AvailableWord mask (values ++ roots) target) (p : properWord mask target) :
    ∃ k t S, k ≤ values.length ∧ LiveWord mask target k t S ∧ ∀ w ∈ S, w ∈ roots := by
  have hm := (hit.resolve_left p.1).resolve_left p.2
  induction values generalizing roots with
  | nil =>
    exact ⟨0, 0, {target}, Nat.zero_le _, LiveWord.stop p, by simpa using hm⟩
  | cons w ws ih =>
    have next : ∀ v ∈ w :: roots, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact maskedGate all builds.1
      · exact all _ hv
    have ht : AvailableWord mask (ws ++ w :: roots) target := by
      exact Or.inr (Or.inr (by simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hm))
    obtain ⟨k, t, S, hk, live, sub⟩ :=
      ih next builds.2 ht ((ht.resolve_left p.1).resolve_left p.2)
    have available : ∀ v ∈ S, v ∈ roots ++ [w] := by
      intro v h
      simpa [or_comm] using sub v h
    obtain ⟨k', t', S', hk', hl, hsub⟩ := pullWord live (classifyWord all builds.1) available
    exact ⟨k', t', S', by simp only [List.length_cons]; omega, hl, hsub⟩

theorem insertWordMem {x w : Nat} {ws : List Nat} :
    x ∈ insertWord w ws ↔ x = w ∨ x ∈ ws := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change x ∈ (if w ≤ a then w :: a :: tail else a :: insertWord w tail) ↔ _
    split <;> simp [ih, or_assoc, or_left_comm]

theorem insertWordNodup {w : Nat} {ws : List Nat} (nd : ws.Nodup) (fresh : w ∉ ws) :
    (insertWord w ws).Nodup := by
  induction ws with
  | nil => simp [insertWord]
  | cons a tail ih =>
    change (if w ≤ a then w :: a :: tail else a :: insertWord w tail).Nodup
    split
    · exact List.nodup_cons.mpr ⟨fresh, nd⟩
    have hn := List.nodup_cons.mp nd
    have hnot : w ≠ a ∧ w ∉ tail := by simpa using fresh
    exact List.nodup_cons.mpr ⟨by simp [insertWordMem, hnot.1.symm, hn.1], ih hn.2 hnot.2⟩

theorem insertWordSet (w : Nat) (ws : List Nat) :
    (insertWord w ws).toFinset = insert w ws.toFinset := by
  ext x
  simp [insertWordMem]

theorem eraseWordSet {ws : List Nat} (nd : ws.Nodup) (w : Nat) :
    (ws.erase w).toFinset = ws.toFinset.erase w := by
  ext x
  simp [nd.mem_erase_iff, and_comm]

theorem gateTokenFields {a b op keep : Nat} (hb : b < 64) (ho : op < 3) (hk : keep < 4) :
    gateToken a b op keep % 4 = keep ∧
    gateToken a b op keep / 4 % 3 = op ∧
    gateToken a b op keep / (4 * 3 * 64) = a ∧
    gateToken a b op keep / (4 * 3) % 64 = b := by
  unfold gateToken
  omega

def keepWord (save : Bool) (w : Nat) (ws : List Nat) : List Nat :=
  if save then ws else ws.erase w

theorem keepNodup {ws : List Nat} (nd : ws.Nodup) (save : Bool) (w : Nat) :
    (keepWord save w ws).Nodup := by
  cases save
  · exact nd.erase _
  · exact nd

theorem keepSubset (save : Bool) (w : Nat) (ws : List Nat) :
    ∀ v ∈ keepWord save w ws, v ∈ ws := by
  cases save
  · exact fun _ h => List.mem_of_mem_erase h
  · exact fun _ h => h

theorem keepSet {ws : List Nat} (nd : ws.Nodup) {w : Nat} {U : Finset Nat}
    (eq : ws.toFinset = insert w U) :
    (keepWord (decide (w ∈ U)) w ws).toFinset = U := by
  by_cases hw : w ∈ U
  · simp [keepWord, hw, eq, Finset.insert_eq_of_mem hw]
  · simp [keepWord, hw, eraseWordSet nd, eq]

theorem keepPairSet {ws : List Nat} (nd : ws.Nodup) {a b : Nat} {U : Finset Nat}
    (ab : a ≠ b) (eq : ws.toFinset = insert a (insert b U)) :
    (keepWord (decide (b ∈ U)) b (keepWord (decide (a ∈ U)) a ws)).toFinset = U := by
  have x : decide (a ∈ insert b U) = decide (a ∈ U) := by simp [ab]
  have h := keepSet nd eq
  rw [x] at h
  exact keepSet (keepNodup nd _ _) h

theorem getWord {ws : List Nat} {x : Nat} (h : x ∈ ws) :
    ws.getD (ws.idxOf x) 0 = x := by
  have inb := List.idxOf_lt_length_iff.mpr h
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inb] using
    List.getElem_idxOf inb

theorem unaryChild {mask fuel a : Nat} {ws : List Nat}
    {history : List (Nat × Nat × Nat)} {x : Nat} {keep : Nat}
    (ha : a < ws.length) (ha64 : a < 64) (hf : fuel ≠ 0) (hk : keep < 2)
    (hx : ws.getD a 0 = x) (p : properWord mask (mask ^^^ x)) (fresh : mask ^^^ x ∉ ws) :
    childState mask (gateToken a a 2 keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (mask ^^^ x) (keepWord (keep.testBit 0) x ws),
        (mask ^^^ x, x, x) :: history) := by
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) ha64 (by decide : 2 < 3) (by omega : keep < 4)
  simp only [childState, ke, op, aa, bb, hx]
  simp [hf, Nat.not_le_of_lt ha, Nat.not_le_of_lt hk, p.1, p.2, fresh, keepWord]

theorem binaryChild {mask fuel a b : Nat} {ws : List Nat}
    {history : List (Nat × Nat × Nat)} {x y : Nat} {keep : Nat}
    (d : Bool) (hab : a < b) (hb : b < ws.length) (hb64 : b < 64)
    (hf : fuel ≠ 0) (hk : keep < 4)
    (hx : ws.getD a 0 = x) (hy : ws.getD b 0 = y)
    (p : properWord mask (binWord d x y)) (fresh : binWord d x y ∉ ws) :
    childState mask (gateToken a b (if d then 1 else 0) keep) (fuel, ws, history) =
      some (fuel - 1, insertWord (binWord d x y)
        (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)),
        (binWord d x y, x, y) :: history) := by
  have oh : (if d then 1 else 0) < 3 := by cases d <;> decide
  obtain ⟨ke, op, aa, bb⟩ := gateTokenFields (a := a) hb64 oh hk
  simp only [childState, ke, op, aa, bb, hx, hy]
  cases d <;>
    simp_all [Nat.not_le_of_lt hab, Nat.not_le_of_lt hb, keepWord, binWord, properWord]

def WordViable (mask : Nat) (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Prop :=
  state.2.1.Nodup ∧ ∃ k t, k ≤ state.1 ∧ LiveWord mask target k t state.2.1.toFinset

def HasChild (mask : Nat) (state child : (Nat × List Nat × List (Nat × Nat × Nat))) : Prop :=
  ∃ a b op keep, a < state.2.1.length ∧
    ((a = b ∧ op = 2 ∧ keep < 2) ∨
      (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4)) ∧
    childState mask (gateToken a b op keep) state = some child

theorem unaryProgress {mask fuel k t : Nat} {x target : Nat} {U : Finset Nat} {ws : List Nat}
    {history : List (Nat × Nat × Nat)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x U) (fresh : mask ^^^ x ∉ insert x U)
    (tail : LiveWord mask target k t (insert (mask ^^^ x) U)) :
    ∃ child, HasChild mask (fuel, ws, history) child ∧ WordViable mask target child := by
  let a := ws.idxOf x
  have xm : x ∈ ws := by
    rw [← List.mem_toFinset, he]
    simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hx : ws.getD a 0 = x := getWord xm
  have p := liveWordProper tail (mask ^^^ x) (Finset.mem_insert_self _ _)
  let save := decide (x ∈ U)
  let keep := if save then 1 else 0
  have keepLt : keep < 2 := by dsimp [keep]; split <;> decide
  have keepBit : keep.testBit 0 = save := by
    unfold keep
    cases save <;> decide
  have fn : mask ^^^ x ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord save x ws
  let child : (Nat × List Nat × List (Nat × Nat × Nat)) := (fuel - 1, insertWord (mask ^^^ x) rest, (mask ^^^ x, x, x) :: history)
  refine ⟨child, ⟨a, a, 2, keep, ha, Or.inl ⟨rfl, rfl, keepLt⟩, ?_⟩, ?_⟩
  · have eq := unaryChild (fuel := fuel) (history := history) ha (by omega) (by omega) keepLt hx p fn
    rw [keepBit] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup nd save x) (fun h => fn (keepSubset save x ws _ h)),
      k, t, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k t (insertWord (mask ^^^ x) rest).toFinset
    rw [insertWordSet, keepSet nd he]
    exact tail

theorem binaryProgress {mask fuel k t : Nat} {x y target : Nat} {d : Bool} {U : Finset Nat}
    {ws : List Nat} {history : List (Nat × Nat × Nat)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hk : k + 1 ≤ fuel)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : binWord d x y ∉ insert x (insert y U))
    (tail : LiveWord mask target k t (insert (binWord d x y) U)) :
    ∃ child, HasChild mask (fuel, ws, history) child ∧ WordViable mask target child := by
  let a := ws.idxOf x
  let b := ws.idxOf y
  have xm : x ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ym : y ∈ ws := by rw [← List.mem_toFinset, he]; simp
  have ha : a < ws.length := List.idxOf_lt_length_iff.mpr xm
  have hb : b < ws.length := List.idxOf_lt_length_iff.mpr ym
  have hab : a < b := ordered
  have hx : ws.getD a 0 = x := getWord xm
  have hy : ws.getD b 0 = y := getWord ym
  let v := binWord d x y
  have p := liveWordProper tail v (Finset.mem_insert_self _ _)
  let saveX := decide (x ∈ U)
  let saveY := decide (y ∈ U)
  let keep := (if saveX then 1 else 0) + (if saveY then 2 else 0)
  have fields : keep < 4 ∧ keep.testBit 0 = saveX ∧ keep.testBit 1 = saveY := by
    unfold keep
    cases saveX <;> cases saveY <;> decide
  obtain ⟨keepLt, bx, by'⟩ := fields
  have fn : v ∉ ws := by simpa [← List.mem_toFinset, he] using fresh
  let rest := keepWord saveY y (keepWord saveX x ws)
  let child : (Nat × List Nat × List (Nat × Nat × Nat)) := (fuel - 1, insertWord v rest, (v, x, y) :: history)
  refine ⟨child, ⟨a, b, if d then 1 else 0, keep, ha, Or.inr ⟨hab, hb, ?_, keepLt⟩, ?_⟩, ?_⟩
  · cases d <;> decide
  · have eq := binaryChild (fuel := fuel) (history := history) d hab hb (by omega) (by omega) keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), k, t, by change k ≤ fuel - 1; omega, ?_⟩
    change LiveWord mask target k t (insertWord v rest).toFinset
    rw [insertWordSet, keepPairSet nd xy he]
    exact tail

theorem wordProgress {mask : Nat} {target : Nat} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (width : state.2.1.length ≤ 64) (h : WordViable mask target state) :
    target ∈ state.2.1 ∨ ∃ child, HasChild mask state child ∧ WordViable mask target child := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨nd, k, t, cap, live⟩ := h
  cases k with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    left
    change ws.toFinset = {target} at eq
    rw [← List.mem_toFinset, eq]
    simp
  | succ k =>
    right
    rcases live with ⟨u,U,x,_,eq,px,fresh,tail⟩ | ⟨U,x,y,d,eq,px,py,xy,fresh,tail⟩
    · exact unaryProgress nd width cap eq fresh tail
    have xm : x ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, eq]; simp
    have diff : ws.idxOf x ≠ ws.idxOf y := by
      intro same
      apply xy
      rw [← getWord xm, same, getWord ym]
    by_cases h : ws.idxOf x < ws.idxOf y
    · exact binaryProgress nd width cap eq xy h fresh tail
    · have eq' : ws.toFinset = insert y (insert x U) := by rw [eq, Finset.insert_comm]
      have fresh' : binWord d y x ∉ insert y (insert x U) := by
        rw [binWord_comm d y x, Finset.insert_comm]; exact fresh
      have tail' : LiveWord mask target k t (insert (binWord d y x) U) := by
        rw [binWord_comm d y x]; exact tail
      exact binaryProgress nd width cap eq' xy.symm (by omega) fresh' tail'

theorem rootWordSublist (base : List Nat) (token : Nat) : (rootWords base token).Sublist base := by
  induction base generalizing token with
  | nil => exact List.Sublist.slnil
  | cons w ws ih =>
    change (if token &&& 1 == 0 then rootWords ws (token >>> 1)
      else w :: rootWords ws (token >>> 1)).Sublist (w :: ws)
    split
    · exact (ih _).cons _
    · exact (ih _).cons₂ _

theorem rootToken (base : List Nat) (S : Finset Nat) :
    ∃ token < 2 ^ base.length, (rootWords base token).toFinset = base.toFinset ∩ S := by
  induction base with
  | nil => exact ⟨0, by simp, by simp [rootWords]⟩
  | cons w ws ih =>
    obtain ⟨token, htoken, ih⟩ := ih
    let bit : Nat := if w ∈ S then 1 else 0
    have hbit : bit < 2 := by dsimp [bit]; split <;> decide
    let code := 2 * token + bit
    have low : code &&& 1 = bit := by
      rw [show (1 : Nat) = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
      dsimp [code]
      omega
    have high : code >>> 1 = token := by
      rw [Nat.shiftRight_eq_div_pow]
      change code / 2 = token
      dsimp [code]
      omega
    refine ⟨code, ?_, ?_⟩
    · simp only [List.length_cons, pow_succ]
      dsimp [code]
      omega
    · change (if code &&& 1 == 0 then rootWords ws (code >>> 1)
        else w :: rootWords ws (code >>> 1)).toFinset = _
      rw [low, high]
      by_cases hw : w ∈ S
      · simp [bit, hw, ih]
      · simp [bit, hw, ih]

theorem liveAgrees {i j k t : Nat} {S : Finset Nat}
    (h : LiveWord mask target k t S) (m : AgreesAt i j mask)
    (all : ∀ w ∈ S, AgreesAt i j w) : AgreesAt i j target := by
  induction h using LiveWord.ind with
  | stop => exact all _ (Finset.mem_singleton_self _)
  | @unary k t U a pa fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · simp only [AgreesAt, Nat.testBit_xor]
      rw [show mask.testBit i = mask.testBit j from m,
        show a.testBit i = a.testBit j from all a (Finset.mem_insert_self _ _)]
    · exact all _ (Finset.mem_insert_of_mem hw)
  | @binary k t U a b d pa pb ab fresh tail ih =>
    apply ih
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · have aa : a.testBit i = a.testBit j := all a (Finset.mem_insert_self _ _)
      have bb : b.testBit i = b.testBit j := all b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
      cases d <;> simp [AgreesAt, binWord, Nat.testBit_and, Nat.testBit_or, aa, bb]
    · exact all _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw))

theorem positiveInMask {i : Nat} (mt : Masked mask target) (ht : target.testBit i = true) :
    mask.testBit i = true := by
  have h := congrArg (fun n : Nat => n.testBit i) mt
  simpa [Nat.testBit_and, ht] using h

variable {rows : Nat}

def fullMask (rows : Nat) : Nat := 2 ^ rows - 1

theorem toNatMasked (v : BitVec rows) : Masked (fullMask rows) v.toNat := by
  unfold Masked fullMask
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt v.isLt]

theorem notNat (v : BitVec rows) : (~~~v).toNat = fullMask rows ^^^ v.toNat := by
  rw [← BitVec.xor_allOnes, BitVec.toNat_xor, Nat.xor_comm, BitVec.toNat_allOnes]
  rfl

theorem gateOfAvailable {bank : List Nat} {w : Nat}
    (av : AvailableWord mask bank w) : GateWord mask bank w :=
  Or.inr ⟨w, 0, av, Or.inl rfl, Or.inr (by simp)⟩

theorem toNatAvailable (bank : List (BitVec rows)) (i : Nat) :
    AvailableWord (fullMask rows) (bank.map BitVec.toNat) (bank.getD i 0).toNat := by
  rw [List.getD_eq_getElem?_getD]
  cases h : bank[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (Or.inr (List.mem_map_of_mem (List.mem_of_getElem? h)))

def buildable (m g : Nat) : Nat → Finset (Nat) → Prop
  | 0, s => g ∈ s
  | n+1, s => buildable m g n s ∨
    (∃ a ∈ s, buildable m g n (insert (m ^^^ a) s)) ∨
    (∃ a ∈ s, ∃ b ∈ s, ∃ d, buildable m g n (insert (binWord d a b) s))

theorem supplyPool {m g : Nat} {n s q} (sub : s ⊆ q) (h : buildable m g n s) : buildable m g n q := by
  induction n generalizing s q with
  | zero => exact sub h
  | succ n ih =>
    rcases h with h | ⟨a,ha,h⟩ | ⟨a,ha,b,hb,d,h⟩
    · exact Or.inl (ih sub h)
    · exact Or.inr (Or.inl ⟨a,sub ha,ih (Finset.insert_subset_insert _ sub) h⟩)
    · exact Or.inr (Or.inr ⟨a,sub ha,b,sub hb,d,ih (Finset.insert_subset_insert _ sub) h⟩)

theorem supplyMore {m g : Nat} {n l s} (le : n ≤ l) (h : buildable m g n s) : buildable m g l s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

abbrev maskedFlat (m a : Nat) : Prop := a &&& m = 0 ∨ a &&& m = m


def flatSet (m : Nat) (s : Finset (Nat)) := s.filter (maskedFlat m)
def visibleWords (m : Nat) (s : Finset (Nat)) := s.image fun w => w &&& m

theorem flIns {m a : Nat} {s : Finset (Nat)} (ha : a ∉ s) :
    (flatSet m (insert a s)).card = (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases f : maskedFlat m a <;> simp [flatSet,Finset.filter_insert,f,ha]

theorem flLe (m a : Nat) (s : Finset (Nat)) :
    (flatSet m (insert a s)).card ≤ (flatSet m s).card + (if maskedFlat m a then 1 else 0) := by
  by_cases old : a ∈ s
  · rw [Finset.insert_eq_of_mem old]
    omega
  · rw [flIns old]

theorem prIns (m a : Nat) (s : Finset (Nat)) :
    visibleWords m (insert a s) = insert (a &&& m) (visibleWords m s) := Finset.image_insert ..

theorem cofNot {mask m : Nat} (sub : mask &&& m = m) (a : Nat) :
    (mask ^^^ a) &&& m = m ^^^ (a &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  have h := congrArg (fun w : Nat => w.testBit i) sub
  simp only [Nat.testBit_and, Nat.testBit_xor] at h ⊢
  cases he : m.testBit i
  · simp
  · have hm : mask.testBit i = true := by simpa [he] using h
    simp [hm]

theorem cofBinary (m a b : Nat) (d : Bool) :
    binWord d a b &&& m = binWord d (a &&& m) (b &&& m) := by
  apply Nat.eq_of_testBit_eq
  intro i
  cases d <;> simp only [binWord, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and, Nat.testBit_or] <;>
    cases m.testBit i <;> simp

theorem flNot {mask m : Nat} (sub : mask &&& m = m) (a : Nat) :
    maskedFlat m (mask ^^^ a) ↔ maskedFlat m a := by
  unfold maskedFlat
  rw [cofNot sub]
  constructor <;> intro h
  · rcases h with h | h
    · right
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
    · left
      have hh := congrArg (fun v => m ^^^ v) h
      simpa [← Nat.xor_assoc] using hh
  · rcases h with h | h <;> simp [h]

theorem flBoth {m a b : Nat} {d : Bool} (ha : maskedFlat m a) (hb : maskedFlat m b) :
    maskedFlat m (binWord d a b) := by
  unfold maskedFlat at *
  rw [cofBinary]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> cases d <;>
    simp [binWord, ha, hb]

theorem simpleBin {m a b : Nat} {d : Bool} (h : maskedFlat m a ∨ maskedFlat m b) :
    binWord d a b &&& m = 0 ∨ binWord d a b &&& m = m ∨
      binWord d a b &&& m = a &&& m ∨ binWord d a b &&& m = b &&& m := by
  rw [cofBinary]
  have top1 (x : Nat) : m &&& (x &&& m) = x &&& m := by
    rw [Nat.land_comm x m, ← Nat.land_assoc]
    simp
  have top2 (x : Nat) : m ||| (x &&& m) = m := by
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_or, Nat.testBit_and]
    cases x.testBit i <;> cases m.testBit i <;> rfl
  have right1 (x : Nat) : (x &&& m) &&& m = x &&& m := restrictWord m x
  have right2 (x : Nat) : (x &&& m) ||| m = m := by rw [Nat.lor_comm, top2]
  rcases h with (ha|ha)|(hb|hb) <;> cases d <;>
    simp [binWord, *, top1, top2, right1, right2]

def projectedStock (m : Nat) (s : Finset (Nat)) := insert 0 (insert m (visibleWords m s))

theorem maskedBuild {goal : Nat} {k t s} (run : LiveWord mask goal k t s) (m : Nat) (submask : mask &&& m = m) (properGoal : ¬ maskedFlat m goal) :
    ∃ n, n+(flatSet m s).card ≤ k ∧ buildable m (goal &&& m) n (projectedStock m s) := by
  induction run using LiveWord.ind with
  | stop =>
    refine ⟨0,?_,?_⟩
    · simp only [flatSet, Finset.filter_singleton, properGoal, ite_false, Finset.card_empty,
        Nat.add_zero, Nat.le_refl]
    · change goal &&& m ∈ projectedStock m {goal}
      simp [projectedStock,visibleWords]
  | @unary k t u a pa fresh tail ih =>
    obtain ⟨n,cap,built⟩ := ih
    have nn : (mask ^^^ a) ∉ u := fun h => fresh (Finset.mem_insert_of_mem h)
    rw [flIns nn] at cap
    have card := flLe m a u
    have old : a &&& m ∈ projectedStock m (insert a u) := by simp [projectedStock,prIns]
    have sub : projectedStock m u ⊆ projectedStock m (insert a u) := by
      exact Finset.insert_subset_insert _ (Finset.insert_subset_insert _ (Finset.image_subset_image (Finset.subset_insert ..)))
    by_cases f : maskedFlat m a
    · have ff := (flNot submask a).mpr f
      simp only [f,ff,ite_true] at cap card
      refine ⟨n,by omega,supplyPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with rfl|rfl|rfl|h
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · rcases ff with e|e
        · exact Or.inl e
        · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inr h))
    · have nf := mt (flNot submask a).mp f
      simp only [f,nf,ite_false] at cap card
      refine ⟨n+1,by omega,Or.inr (Or.inl ⟨_,old,supplyPool ?_ built⟩)⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rw [cofNot submask] at hw
      tauto
  | @binary k t u a b d pa pb ab fresh tail ih =>
    let v := binWord d a b
    obtain ⟨n,cap,built⟩ := ih
    have nn : v ∉ u := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    change n+(flatSet m (insert v u)).card ≤ k at cap
    rw [flIns nn] at cap
    have ca := flLe m a (insert b u)
    have cb := flLe m b u
    by_cases simple : maskedFlat m a ∨ maskedFlat m b
    · have budget : n + (flatSet m (insert a (insert b u))).card ≤ k+1 := by
        by_cases fa : maskedFlat m a <;> by_cases fb : maskedFlat m b <;>
          simp only [fa,fb,ite_true,ite_false] at ca cb simple
        all_goals first | have vf : maskedFlat m v := flBoth fa fb; simp only [vf,ite_true] at cap; omega | omega | tauto
      refine ⟨n,budget,supplyPool ?_ built⟩
      intro w hw
      simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
      rcases hw with e|e|e|e
      · exact Or.inl e
      · exact Or.inr (Or.inl e)
      · subst w
        have cases := simpleBin (d := d) simple
        tauto
      · tauto
    · have fa : ¬maskedFlat m a := fun h => simple (Or.inl h)
      have fb : ¬maskedFlat m b := fun h => simple (Or.inr h)
      simp only [fa,fb,ite_false] at ca cb
      refine ⟨n+1,by omega,Or.inr (Or.inr ⟨a &&& m,?_,b &&& m,?_,d,supplyPool ?_ built⟩)⟩
      · simp [projectedStock,prIns]
      · simp [projectedStock,prIns]
      · intro w hw
        simp only [projectedStock,prIns,Finset.mem_insert] at hw ⊢
        rw [cofBinary] at hw
        tauto

theorem availableB_spec {mask : Nat} {bank : List Nat} {v : Nat} :
    availableB mask bank v = true ↔ AvailableWord mask bank v := by
  simp [availableB, AvailableWord, or_assoc]

theorem recipeGate_spec {mask : Nat} {bank : List Nat} {v a b : Nat}
    (h : recipeGate mask bank v a b = true) : GateWord mask bank v := by
  simp only [recipeGate, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, availableB_spec] at h
  rcases h with ⟨ha, first | ⟨hb, second⟩⟩
  · exact Or.inl ⟨a, ha, first⟩
  · exact Or.inr ⟨a, b, ha, hb, second⟩

theorem replayRecipesBuilds (mask : Nat) (needed : List Nat) (recipes : List (Nat × Nat × Nat))
    (bank : List Nat) : WordBuilds mask bank (replayRecipes mask needed recipes bank) := by
  induction recipes generalizing bank with
  | nil => trivial
  | cons recipe recipes ih =>
    obtain ⟨w, a, b⟩ := recipe
    change WordBuilds mask bank
      (if needed.contains (w &&& mask) && !availableB mask bank (w &&& mask) &&
          recipeGate mask bank (w &&& mask) (a &&& mask) (b &&& mask) then
        (w &&& mask) :: replayRecipes mask needed recipes ((w &&& mask) :: bank)
      else replayRecipes mask needed recipes bank)
    split
    · rename_i yes
      exact ⟨recipeGate_spec (Bool.and_eq_true_iff.mp yes).2, ih _⟩
    · exact ih _

theorem flatCountCard (mask : Nat) {words : List Nat} (nodup : words.Nodup) :
    flatCount mask words = (flatSet mask words.toFinset).card := by
  induction words with
  | nil => rfl
  | cons w ws ih =>
    have nd := List.nodup_cons.mp nodup
    have fresh : w ∉ ws.toFinset := by simpa using nd.1
    have bool : maskFlat mask w = true ↔ maskedFlat mask w := by
      simp [maskFlat, maskedFlat]
    change (if maskFlat mask w then flatCount mask ws + 1 else flatCount mask ws) = _
    rw [List.toFinset_cons, flIns fresh, ih nd.2]
    by_cases h : maskedFlat mask w
    · simp [h, bool.mpr h]
    · have no : maskFlat mask w = false := Bool.eq_false_iff.mpr (fun ht => h (bool.mp ht))
      simp [h, no]

theorem buildsAppend {mask : Nat} {roots first second : List Nat}
    (left : WordBuilds mask roots first)
    (right : WordBuilds mask (first ++ roots) second) :
    WordBuilds mask roots (first ++ second) := by
  induction first generalizing roots with
  | nil => exact right
  | cons w ws ih =>
    refine ⟨left.1, ih left.2 ?_⟩
    have same (bank other vals : List Nat) (perm : bank.Perm other)
        (h : WordBuilds mask bank vals) : WordBuilds mask other vals := by
      induction vals generalizing bank other with
      | nil => trivial
      | cons v vs ih =>
        exact ⟨gateWeaken (fun x hx => Or.inr (Or.inr (perm.mem_iff.mp hx))) h.1,
          ih _ _ (perm.cons v) h.2⟩
    exact same _ _ _ (List.perm_middle (a := w) (l₁ := ws) (l₂ := roots)).symm right

theorem buildableWords {mask goal n : Nat} {pool : Finset Nat} {bank : List Nat}
    (h : buildable mask goal n pool) (supply : ∀ w ∈ pool, AvailableWord mask bank w) :
    ∃ values, values.length ≤ n ∧ WordBuilds mask bank values ∧
      AvailableWord mask (values ++ bank) goal := by
  induction n generalizing pool bank with
  | zero => exact ⟨[], Nat.le_refl _, trivial, supply _ h⟩
  | succ n ih =>
    have add {w : Nat} (g : GateWord mask bank w)
        (tail : buildable mask goal n (insert w pool)) :
        ∃ values, values.length ≤ n+1 ∧ WordBuilds mask bank values ∧
          AvailableWord mask (values ++ bank) goal := by
      have growing : ∀ v ∈ insert w pool, AvailableWord mask (w :: bank) v := by
        intro v hv
        rcases Finset.mem_insert.mp hv with rfl | hv
        · exact Or.inr (Or.inr List.mem_cons_self)
        · exact availableWeaken (fun _ hh => Or.inr (Or.inr (List.mem_cons_of_mem _ hh))) (supply _ hv)
      obtain ⟨values, budget, build, hit⟩ := ih tail growing
      refine ⟨w :: values, by simp only [List.length_cons]; omega, ⟨g, build⟩, ?_⟩
      rcases hit with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (by simp only [List.mem_append, List.mem_cons] at *; tauto))
    rcases h with h | ⟨a, ha, h⟩ | ⟨a, ha, b, hb, d, h⟩
    · obtain ⟨values, cap, build, hit⟩ := ih h supply
      exact ⟨values, by omega, build, hit⟩
    · exact add (Or.inl ⟨a, supply a ha, rfl⟩) h
    · apply add (w := binWord d a b) ?_ h
      exact Or.inr ⟨a, b, supply a ha, supply b hb, by cases d <;> simp [binWord]⟩

theorem boundClosesSound {state : (Nat × List Nat × List (Nat × Nat × Nat))} {bound : (Nat × List Nat × Nat × Nat)}
    (known : Lower bound.1 bound.2.1 bound.2.2.2 bound.2.2.1)
    (submask : mask &&& bound.1 = bound.1)
    (viable : WordViable mask target state) :
    boundCloses target state bound = false := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨cut, stock, minimum, goal⟩ := bound
  obtain ⟨nd, k, t, steps, live⟩ := viable
  change k ≤ fuel at steps
  change LiveWord mask target k t ws.toFinset at live
  apply Bool.eq_false_iff.mpr
  intro hc
  let replay := replayRecipes cut (recipeNeeded cut stock ws history) history.reverse stock
  change ((target &&& cut) == goal && goal != 0 && goal != cut &&
    (if fuel - flatCount cut ws < minimum then
      if (recipeStart cut stock ws).length + (fuel - flatCount cut ws) < minimum then
        if (recipeNeeded cut stock ws history).length + (fuel - flatCount cut ws) < minimum then
          (replay.length + (fuel - flatCount cut ws) < minimum) &&
            ws.all (fun w => availableB cut (replay ++ stock) (w &&& cut))
        else false
      else false
    else false)) = true at hc
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hc
  obtain ⟨⟨⟨goalEq, nonzero⟩, nonflat⟩, scan⟩ := hc
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  split at scan <;> try contradiction
  rcases Bool.and_eq_true_iff.mp scan with ⟨length, sources⟩
  simp only [decide_eq_true_eq] at length
  have pn : ¬maskedFlat cut target := by simpa [maskedFlat, goalEq] using And.intro nonzero nonflat
  obtain ⟨n, hn, build⟩ := maskedBuild live cut submask pn
  rw [← flatCountCard cut nd] at hn
  change n + flatCount cut ws ≤ k at hn
  have supply : ∀ w ∈ projectedStock cut ws.toFinset, AvailableWord cut (replay ++ stock) w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image,
      List.mem_toFinset] at hw
    rcases hw with rfl | rfl | ⟨v, hv, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact availableB_spec.mp (List.all_eq_true.mp sources v hv)
  obtain ⟨ys, hy, built, avail⟩ := buildableWords build supply
  have both := buildsAppend (replayRecipesBuilds cut _ history.reverse stock) built
  have hit : AvailableWord cut ((replay ++ ys) ++ stock) goal := by
    rw [← goalEq]
    exact availableWeaken (fun v hv => Or.inr (Or.inr (by
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using hv))) avail
  have enough := known (replay ++ ys) both hit
  simp only [List.length_append] at enough
  omega

theorem knownClosesSound {bounds : List (Nat × List Nat × Nat × Nat)} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (known : Known bounds) (submask : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (viable : WordViable mask target state) :
    knownCloses target bounds state = false := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (boundCloses target state bound || knownCloses target bounds state) = false
    rw [boundClosesSound (known _ List.mem_cons_self) (submask _ List.mem_cons_self) viable]
    exact ih (fun b hb => known b (List.mem_cons_of_mem _ hb))
      (fun b hb => submask b (List.mem_cons_of_mem _ hb))

def encodePoint (f : (Fin rows → Bool)) : BitVec rows :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast List.length_ofFn

theorem encodeBit (f : (Fin rows → Bool)) (i : Fin rows) :
    (encodePoint f).getLsbD i.val = f i := by
  simp only [encodePoint, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [i.isLt]

theorem encodeNot (f : (Fin rows → Bool)) : encodePoint (fun j => !f j) = ~~~encodePoint f := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_not, encodeBit f ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
  simp [hi]

theorem encodeAnd (a b : (Fin rows → Bool)) :
    encodePoint (fun i => a i && b i) = encodePoint a &&& encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]

theorem encodeOr (a b : (Fin rows → Bool)) :
    encodePoint (fun i => a i || b i) = encodePoint a ||| encodePoint b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_or, encodeBit a ⟨i, hi⟩, encodeBit b ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]

def pointWord (f : (Fin rows → Bool)) : Nat := (encodePoint f).toNat

def relabel (sourceIndex : Fin rows → Fin rows) (word : Nat) : Nat :=
  pointWord fun i => word.testBit (sourceIndex i).val

theorem maskBit {i : Nat} (hi : i < rows) : (fullMask rows).testBit i = true := by
  simp [fullMask, Nat.testBit_two_pow_sub_one, hi]

theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp
  simp [pointWord, eq]

theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))

theorem relabelMask (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex (fullMask rows) = fullMask rows := by
  have all : (fun i => (fullMask rows).testBit (sourceIndex i).val) = fun _ => true := by
    funext i
    exact maskBit (sourceIndex i).isLt
  have bits : encodePoint (fun _ : Fin rows => true) = BitVec.allOnes rows := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp [hi]
  simp [relabel, all, pointWord, bits, fullMask]

theorem relabelNot (sourceIndex : Fin rows → Fin rows) (a : Nat) :
    relabel sourceIndex (fullMask rows ^^^ a) = fullMask rows ^^^ relabel sourceIndex a := by
  have eq : (fun i => (fullMask rows ^^^ a).testBit (sourceIndex i).val) =
      fun i => !a.testBit (sourceIndex i).val := by
    funext i
    simp [Nat.testBit_xor, maskBit (sourceIndex i).isLt]
  simp only [relabel, eq, pointWord, encodeNot, notNat]

theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Nat) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]

theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Nat) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]

theorem lowerRelabel (sourceIndex : Fin rows → Fin rows) {bank roots : List Nat}
    {src dst : Nat} {minimum : Nat}
    (old : Lower (fullMask rows) bank src minimum)
    (goal : relabel sourceIndex dst = src)
    (supply : ∀ w ∈ roots, AvailableWord (fullMask rows) bank (relabel sourceIndex w)) :
    Lower (fullMask rows) roots dst minimum := by
  apply lowerMap (relabel sourceIndex) (relabelZero sourceIndex) (relabelMask sourceIndex)
    (relabelNot sourceIndex) (relabelAnd sourceIndex) (relabelOr sourceIndex) supply
  rw [goal]
  exact old

theorem relabelXor (sourceIndex : Fin rows → Fin rows) (a b : Nat) :
    relabel sourceIndex (a ^^^ b) = relabel sourceIndex a ^^^ relabel sourceIndex b := by
  have eq : encodePoint (fun i => (a ^^^ b).testBit (sourceIndex i).val) =
      encodePoint (fun i => a.testBit (sourceIndex i).val) ^^^
      encodePoint (fun i => b.testBit (sourceIndex i).val) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_xor, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩, encodeBit _ ⟨i, hi⟩]
    exact Nat.testBit_xor ..
  simpa only [relabel, pointWord, BitVec.toNat_xor] using congrArg BitVec.toNat eq

theorem lowerRelabelMasked (sourceIndex : Fin rows → Fin rows)
    {oldMask newMask : Nat} {bank roots : List Nat} {src dst : Nat} {minimum : Nat}
    (old : Lower oldMask bank src minimum)
    (masks : relabel sourceIndex newMask = oldMask)
    (goal : relabel sourceIndex dst = src)
    (supply : ∀ w ∈ roots, AvailableWord oldMask bank (relabel sourceIndex w)) :
    Lower newMask roots dst minimum := by
  apply lowerMap (relabel sourceIndex) (relabelZero sourceIndex) masks
    (fun w => by rw [relabelXor, masks]) (relabelAnd sourceIndex) (relabelOr sourceIndex) supply
  rwa [goal]

theorem extendKnownRelabel (sourceIndex : Fin rows → Fin rows) {bounds : List (Nat × List Nat × Nat × Nat)}
    {source destination : (Nat × List Nat × Nat × Nat)} (old : Known bounds) (mem : source ∈ bounds)
    (budget : destination.2.2.1 = source.2.2.1)
    (masks : relabel sourceIndex destination.1 = source.1)
    (goal : relabel sourceIndex destination.2.2.2 = source.2.2.2)
    (supply : ∀ w ∈ destination.2.1,
      AvailableWord source.1 source.2.1 (relabel sourceIndex w)) :
    Known (destination :: bounds) := by
  apply extendKnown old
  rw [budget]
  exact lowerRelabelMasked sourceIndex (old _ mem) masks goal supply

theorem relabelToNatBound (sourceIndex : Fin rows → Fin rows) (word : Nat) :
    Masked (fullMask rows) (relabel sourceIndex word) := toNatMasked _

theorem relabelBit (sourceIndex : Fin rows → Fin rows) (word : Nat) (i : Fin rows) :
    (relabel sourceIndex word).testBit i.val = word.testBit (sourceIndex i).val :=
  encodeBit _ i

theorem relabelOutside (sourceIndex : Fin rows → Fin rows) (word i : Nat) (h : rows ≤ i) :
    (relabel sourceIndex word).testBit i = false := by
  apply Nat.testBit_lt_two_pow
  exact Nat.lt_of_lt_of_le (show (encodePoint _).toNat < 2 ^ rows from BitVec.isLt _)
    (Nat.pow_le_pow_right (by decide) h)

theorem relabelInj (sourceIndex : Fin rows → Fin rows) (onto : Function.Surjective sourceIndex)
    {a b : Nat} (ba : Masked (fullMask rows) a) (bb : Masked (fullMask rows) b)
    (eq : relabel sourceIndex a = relabel sourceIndex b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · obtain ⟨j, h⟩ := onto ⟨i, inside⟩
    have bit := congrArg (fun w : Nat => w.testBit j.val) eq
    simpa only [relabelBit, h] using bit
  · have ea := congrArg (fun w : Nat => w.testBit i) ba
    have eb := congrArg (fun w : Nat => w.testBit i) bb
    simp only [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, inside, decide_false,
      Bool.and_false] at ea eb
    rw [← ea, ← eb]

theorem kw_step (goal : Nat) (D D' : Finset Nat) (u v w : ℕ) (c : ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ)
    (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (huD : u ∉ D') (hvD : v ∉ D')
    (hsub : ∀ x ∈ D', x ≠ w → x ∈ D)
    (hf : ∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ D' ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false)
    (hr : ∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)
    (hcu : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = true →
      u.testBit e = true ∧ u.testBit i = false)
    (hcv : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = false →
      v.testBit e = true ∧ v.testBit i = false)
    (hc : ∀ e i e' i', c e i = c e' i' → c e i' = c e i) :
    ∃ g : ℕ → ℕ → ℕ,
      (∀ e i, goal.testBit e = true → goal.testBit i = false →
        g e i ∈ D ∧ (g e i).testBit e = true ∧ (g e i).testBit i = false) ∧
      (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true → goal.testBit i = false → goal.testBit i' = false → g e i = g e' i' → g e i' = g e i) := by
  have hg : ∀ e i, goal.testBit e = true → goal.testBit i = false → f e i = w →
      ((if f e i = w then (cond (c e i) u v) else f e i) = u ∧ c e i = true) ∨
      ((if f e i = w then (cond (c e i) u v) else f e i) = v ∧ c e i = false) := by
    intro e i _ _ h
    rw [ite_eq_left (h)]
    cases c e i
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  refine ⟨fun e i => if f e i = w then (cond (c e i) u v) else f e i, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1, h2, h3⟩ := hf e i he hi
    show (if f e i = w then (cond (c e i) u v) else f e i) ∈ D ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit e = true ∧
      (if f e i = w then (cond (c e i) u v) else f e i).testBit i = false
    by_cases hw : f e i = w
    · rw [hw] at h2 h3
      rcases hg e i he hi hw with ⟨hx, hcc⟩ | ⟨hx, hcc⟩
      · rw [hx]; exact ⟨hu, hcu e i h2 h3 hcc⟩
      · rw [hx]; exact ⟨hv, hcv e i h2 h3 hcc⟩
    · rw [ite_eq_right (hw)]; exact ⟨hsub _ h1 hw, h2, h3⟩
  · intro e i e' i' he he' hi hi' heq
    show (if f e i' = w then (cond (c e i') u v) else f e i') =
      (if f e i = w then (cond (c e i) u v) else f e i)
    have heq' : (if f e i = w then (cond (c e i) u v) else f e i) =
      (if f e' i' = w then (cond (c e' i') u v) else f e' i') := heq
    by_cases h1 : f e i = w
    · by_cases h2 : f e' i' = w
      · have h3 : f e i' = w := (hr e i e' i' he he' hi hi' (h1.trans h2.symm)).trans h1
        have hcc : c e i = c e' i' := by
          rcases hg e i he hi h1 with ⟨hx, hx'⟩ | ⟨hx, hx'⟩ <;>
            rcases hg e' i' he' hi' h2 with ⟨hy, hy'⟩ | ⟨hy, hy'⟩
          · rw [hx', hy']
          · exact absurd (hx.symm.trans (heq'.trans hy)) huv
          · exact absurd (hy.symm.trans (heq'.symm.trans hx)) huv
          · rw [hx', hy']
        rw [ite_eq_left (h3), ite_eq_left (h1), hc e i e' i' hcc]
      · exfalso
        rw [ite_eq_right (h2)] at heq'
        have hm := (hf e' i' he' hi').1
        rcases hg e i he hi h1 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, heq']; exact hm)
        · exact hvD (by rw [← hx, heq']; exact hm)
    · by_cases h2 : f e' i' = w
      · exfalso
        rw [ite_eq_right (h1)] at heq'
        have hm := (hf e i he hi).1
        rcases hg e' i' he' hi' h2 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, ← heq']; exact hm)
        · exact hvD (by rw [← hx, ← heq']; exact hm)
      · have h1n : (if f e i = w then (cond (c e i) u v) else f e i) = f e i := ite_eq_right h1
        have h2n : (if f e' i' = w then (cond (c e' i') u v) else f e' i') = f e' i' := ite_eq_right h2
        rw [h1n, h2n] at heq'
        have h3 := hr e i e' i' he he' hi hi' heq'
        have h3n : ¬ f e i' = w := by rw [h3]; exact h1
        rw [h1n, ite_eq_right (h3n)]
        exact h3

theorem and_cu (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (_h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_and] at h1
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem and_cv (u v e i : ℕ) (h1 : (u &&& v).testBit e = true) (h2 : (u &&& v).testBit i = false)
    (h3 : (!(u.testBit i)) = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_and] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem or_cu (u v e i : ℕ) (_h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = true) : u.testBit e = true ∧ u.testBit i = false := by
  rw [Nat.testBit_or] at h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

theorem or_cv (u v e i : ℕ) (h1 : (u ||| v).testBit e = true) (h2 : (u ||| v).testBit i = false)
    (h3 : u.testBit e = false) : v.testBit e = true ∧ v.testBit i = false := by
  rw [Nat.testBit_or] at h1 h2
  cases hue : u.testBit e <;> cases hui : u.testBit i <;> simp_all

def KWPartition (goal : Nat) (ws : Finset Nat) : Prop :=
  ∃ f : Nat → Nat → Nat,
    (∀ e i, goal.testBit e = true → goal.testBit i = false →
      f e i ∈ ws ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false) ∧
    (∀ e i e' i', goal.testBit e = true → goal.testBit e' = true →
      goal.testBit i = false → goal.testBit i' = false → f e i = f e' i' → f e i' = f e i)

theorem kwFromLive {mask goal : Nat} {k : Nat} {S : Finset Nat}
    (live : LiveWord mask goal k 0 S) (tight : S.card = k + 1) : KWPartition goal S := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_, eq, _⟩ := live
    subst S
    exact ⟨fun _ _ => goal, fun _ _ hp hn => ⟨by simp, hp, hn⟩, fun _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, eq, _⟩ | ⟨U, a, b, op, rfl, pa, pb, ab, fresh, tail⟩
    · omega
    let w := binWord op a b
    have wU : w ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have wA : w ≠ a := fun eq => fresh (Finset.mem_insert.mpr (Or.inl eq))
    have wB : w ≠ b := fun eq => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl eq)))
    have tailSize := (liveWordSize tail).2
    change (insert w U).card + 0 ≤ k + 1 at tailSize
    rw [Finset.card_insert_of_notMem wU] at tailSize
    have paCard := Finset.card_insert_le a (insert b U)
    have pbCard := Finset.card_insert_le b U
    have aU : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h)] at tight
      omega
    have bU : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight
      have := Finset.card_insert_le a U
      omega
    obtain ⟨f, hf, hr⟩ := ih tail (by
      change (insert w U).card = k + 1
      rw [Finset.card_insert_of_notMem wU]
      omega)
    have keepA : a ∉ insert w U := by simp [wA.symm, aU]
    have keepB : b ∉ insert w U := by simp [wB.symm, bU]
    have other : ∀ x ∈ insert w U, x ≠ w → x ∈ insert a (insert b U) := by
      intro x hx hn
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ((Finset.mem_insert.mp hx).resolve_left hn))
    have ha : a ∈ insert a (insert b U) := Finset.mem_insert_self ..
    have hb : b ∈ insert a (insert b U) := Finset.mem_insert_of_mem (Finset.mem_insert_self ..)
    cases op
    · exact kw_step goal _ _ a b w (fun _ i => !(a.testBit i)) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => and_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => and_cv a b e i h1 h2 h3)
        (fun _ _ _ _ h => h.symm)
    · exact kw_step goal _ _ a b w (fun e _ => a.testBit e) f ha hb ab keepA keepB other hf hr
        (fun e i h1 h2 h3 => or_cu a b e i h1 h2 h3) (fun e i h1 h2 h3 => or_cv a b e i h1 h2 h3)
        (fun _ _ _ _ _ => rfl)

theorem liveDirected {mask goal : Nat} {k : Nat} {S : Finset Nat}
    (live : LiveWord mask goal k 0 S) {p n : Nat}
    (hp : goal.testBit p = true) (hn : goal.testBit n = false) :
    ∃ w ∈ S, w.testBit p = true ∧ w.testBit n = false := by
  induction k generalizing S with
  | zero =>
    obtain ⟨_,rfl,_⟩ := live
    exact ⟨goal, by simp, hp, hn⟩
  | succ k ih =>
    rcases live with ⟨u, U, a, ueq, _⟩ | ⟨U,a,b,op,rfl,pa,pb,ab,fresh,tail⟩
    · omega
    obtain ⟨w, hw, wp, wn⟩ := ih tail
    rcases Finset.mem_insert.mp hw with eq | hU
    · subst w
      cases op
      · by_cases ha : a.testBit n = false
        · exact ⟨a, Finset.mem_insert_self .., and_cu a b p n wp wn (by simp [ha])⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            and_cv a b p n wp wn (by cases h : a.testBit n <;> simp_all)⟩
      · by_cases ha : a.testBit p = true
        · exact ⟨a, Finset.mem_insert_self .., or_cu a b p n wp wn ha⟩
        · exact ⟨b, Finset.mem_insert_of_mem (Finset.mem_insert_self ..),
            or_cv a b p n wp wn (by cases h : a.testBit p <;> simp_all)⟩
    · exact ⟨w, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU),wp,wn⟩

namespace PackedRect

theorem tb4095 (i : ℕ) : (4095 : ℕ).testBit i = decide (i < 12) := by
  have e : (4095 : ℕ) = 2 ^ 12 - 1 := by norm_num
  rw [e, Nat.testBit_two_pow_sub_one]

def tb (w e : ℕ) : Bool := !(Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)

theorem tb_eq (w e : ℕ) : tb w e = w.testBit e := by
  have h : Nat.land (Nat.shiftRight w e) 1 = 1 &&& (w >>> e) := Nat.and_comm _ _
  unfold tb Nat.testBit
  rw [h]
  generalize (1 &&& w >>> e) = X
  cases X <;> rfl

def rect (x J : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)

def rectW (x : ℕ) : ℕ := rect x (Nat.xor (Nat.shiftRight x 12) 4095) 12

theorem rect_tb (x J i : ℕ) (hJ : J.testBit i = true) : ∀ n e : ℕ, e < n → x.testBit e = true →
    (rect x J n).testBit (12 * e + i) = true := by
  intro n
  induction n with
  | zero => intro e he; omega
  | succ n ih =>
    intro e he hx
    show ((cond (tb x n) (J <<< (12 * n)) 0) ||| rect x J n).testBit (12 * e + i) = true
    rw [Nat.testBit_or]
    by_cases hen : e = n
    · subst hen
      rw [tb_eq, hx]
      simp [Nat.testBit_shiftLeft, hJ]
    · rw [ih e (by omega) hx]
      simp

theorem rectW_tb (x e i : ℕ) (he : e < 12) (hi : i < 12) (h1 : x.testBit e = true)
    (h2 : x.testBit (12 + i) = false) : (rectW x).testBit (12 * e + i) = true := by
  apply rect_tb _ _ _ _ 12 e he h1
  show ((x >>> 12) ^^^ 4095).testBit i = true
  rw [Nat.testBit_xor, Nat.testBit_shiftRight, h2, tb4095]
  simp [hi]

def full : ℕ := 22300745198530623141535718272648361505980415

theorem full_eq : full = 2 ^ 144 - 1 := by norm_num [full]

theorem tb_land (a b q : ℕ) : (Nat.land a b).testBit q = (a.testBit q && b.testBit q) :=
  Nat.testBit_and a b q

theorem tb_lor (a b q : ℕ) : (Nat.lor a b).testBit q = (a.testBit q || b.testBit q) :=
  Nat.testBit_or a b q

theorem tb_xor (a b q : ℕ) : (Nat.xor a b).testBit q = Bool.xor (a.testBit q) (b.testBit q) :=
  Nat.testBit_xor a b q

theorem full_tb (q : ℕ) : full.testBit q = decide (q < 144) := by
  rw [full_eq, Nat.testBit_two_pow_sub_one]

theorem land_sub (h a : ℕ) (H : ∀ q, h.testBit q = true → a.testBit q = true) :
    Nat.land h a = h := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land]
  cases hh : h.testBit q
  · rfl
  · rw [H q hh]; rfl

theorem land_disj (a h : ℕ) (H : ∀ q, a.testBit q = true → h.testBit q = true → False) :
    Nat.land a h = 0 := by
  apply Nat.eq_of_testBit_eq
  intro q
  rw [tb_land, Nat.zero_testBit]
  cases ha : a.testBit q
  · rfl
  · cases hh : h.testBit q
    · rfl
    · exact (H q ha hh).elim

def orS (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftRight x s)

def orSL (x s : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft x s)

theorem orS_tb (x s q : ℕ) : (orS x s).testBit q = (x.testBit q || x.testBit (s + q)) := by
  show (x ||| x >>> s).testBit q = _
  rw [Nat.testBit_or, Nat.testBit_shiftRight]

theorem orSL_tb (x s q : ℕ) :
    (orSL x s).testBit q = (x.testBit q || (decide (s ≤ q) && x.testBit (q - s))) := by
  show (x ||| x <<< s).testBit q = _
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft, ge_iff_le]

theorem orS_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ p.testBit (k * j + q) = true) (q : ℕ)
    (h : (orS x (k * s)).testBit q = true) : ∃ j, j < n + s ∧ p.testBit (k * j + q) = true := by
  rw [orS_tb, Bool.or_eq_true] at h
  rcases h with h | h
  · obtain ⟨j, hj, hp⟩ := hx q h
    exact ⟨j, by omega, hp⟩
  · obtain ⟨j, hj, hp⟩ := hx _ h
    refine ⟨j + s, by omega, ?_⟩
    rw [Nat.mul_add, Nat.add_assoc]; exact hp

theorem orSL_ex (k p x n s : ℕ)
    (hx : ∀ q, x.testBit q = true → ∃ j, j < n ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true)
    (q : ℕ) (h : (orSL x (k * s)).testBit q = true) :
    ∃ j, j < n + s ∧ k * j ≤ q ∧ p.testBit (q - k * j) = true := by
  rw [orSL_tb, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with h | ⟨hs, h⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx q h
    exact ⟨j, by omega, hq, hp⟩
  · obtain ⟨j, hj, hq, hp⟩ := hx _ h
    have e : q - k * (j + s) = q - k * s - k * j := by rw [Nat.mul_add]; omega
    refine ⟨j + s, by omega, ?_, ?_⟩
    · rw [Nat.mul_add]; omega
    · rw [e]; exact hp

def rowM : ℕ := 5445847423328601499764522166702896582657

theorem rowM_tb (q : ℕ) (h : rowM.testBit q = true) : q < 144 ∧ q % 12 = 0 := by
  have hlt : q < 144 := by
    by_contra hq
    have h0 : rowM.testBit q = false := by
      apply Nat.testBit_lt_two_pow
      have h1 : rowM < 2 ^ 144 := by norm_num [rowM]
      have h2 : (2 : ℕ) ^ 144 ≤ 2 ^ q := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [h0] at h
    exact Bool.noConfusion h
  have hall : ∀ q : ℕ, q < 144 → rowM.testBit q = true → q % 12 = 0 := by decide +kernel
  exact ⟨hlt, hall q hlt h⟩

def rowsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 6) 3) 1) 1) rowM

def colsOf (p : ℕ) : ℕ := Nat.land (orS (orS (orS (orS p 96) 48) 24) 12) 4095

def hullC (p : ℕ) : ℕ :=
  Nat.land (orSL (orSL (orSL (orSL (rowsOf p) 6) 3) 1) 1)
    (orSL (orSL (orSL (orSL (colsOf p) 96) 48) 24) 12)

def hull (p : ℕ) : ℕ := hullC (Nat.land p full)

theorem rowsOf_tb (p q : ℕ) (h : (rowsOf p).testBit q = true) :
    (q < 144 ∧ q % 12 = 0) ∧ ∃ j, j < 12 ∧ p.testBit (j + q) = true := by
  unfold rowsOf at h
  rw [tb_land, Bool.and_eq_true] at h
  refine ⟨rowM_tb q h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (1 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 1 p _ 1 6 h0
  have h2 := orS_ex 1 p _ _ 3 h1
  have h3 := orS_ex 1 p _ _ 1 h2
  have h4 := orS_ex 1 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, by simpa using hp⟩

theorem colsOf_tb (p q : ℕ) (h : (colsOf p).testBit q = true) :
    q < 12 ∧ ∃ j, j < 16 ∧ p.testBit (12 * j + q) = true := by
  unfold colsOf at h
  rw [tb_land, Bool.and_eq_true, tb4095, decide_eq_true_eq] at h
  refine ⟨h.2, ?_⟩
  have h0 : ∀ q, p.testBit q = true → ∃ j, j < 1 ∧ p.testBit (12 * j + q) = true :=
    fun q hq => ⟨0, by norm_num, by simpa using hq⟩
  have h1 := orS_ex 12 p _ 1 8 h0
  have h2 := orS_ex 12 p _ _ 4 h1
  have h3 := orS_ex 12 p _ _ 2 h2
  have h4 := orS_ex 12 p _ _ 1 h3
  obtain ⟨j, hj, hp⟩ := h4 q h.1
  exact ⟨j, by omega, hp⟩

theorem hullC_spec (p : ℕ) (hp : ∀ q, p.testBit q = true → q < 144) (q : ℕ)
    (h : (hullC p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  unfold hullC at h
  rw [tb_land, Bool.and_eq_true] at h
  obtain ⟨hR, hC⟩ := h
  have r0 : ∀ q, (rowsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 1 * j ≤ q ∧ (rowsOf p).testBit (q - 1 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have r1 := orSL_ex 1 (rowsOf p) _ 1 6 r0
  have r2 := orSL_ex 1 (rowsOf p) _ _ 3 r1
  have r3 := orSL_ex 1 (rowsOf p) _ _ 1 r2
  have r4 := orSL_ex 1 (rowsOf p) _ _ 1 r3
  obtain ⟨j, hj, hjq, hr⟩ := r4 q hR
  obtain ⟨⟨hb, hm⟩, i, hi, hpi⟩ := rowsOf_tb p _ hr
  have c0 : ∀ q, (colsOf p).testBit q = true →
      ∃ j, j < 1 ∧ 12 * j ≤ q ∧ (colsOf p).testBit (q - 12 * j) = true :=
    fun q hq => ⟨0, by norm_num, by omega, by simpa using hq⟩
  have c1 := orSL_ex 12 (colsOf p) _ 1 8 c0
  have c2 := orSL_ex 12 (colsOf p) _ _ 4 c1
  have c3 := orSL_ex 12 (colsOf p) _ _ 2 c2
  have c4 := orSL_ex 12 (colsOf p) _ _ 1 c3
  obtain ⟨j', hj', hjq', hc⟩ := c4 q hC
  obtain ⟨hlt, e', he', hpe⟩ := colsOf_tb p _ hc
  have e1 : i + (q - 1 * j) = 12 * (q / 12) + i := by omega
  have e2 : q - 12 * j' = q % 12 := by omega
  rw [e1] at hpi
  rw [e2] at hpe
  have hb' := hp _ hpe
  exact ⟨by omega, i, e', hi, by omega, hpi, hpe⟩

theorem hull_spec (p q : ℕ) (h : (hull p).testBit q = true) :
    q < 144 ∧ ∃ i e', i < 12 ∧ e' < 12 ∧ p.testBit (12 * (q / 12) + i) = true ∧
      p.testBit (12 * e' + q % 12) = true := by
  have hp : ∀ q, (Nat.land p full).testBit q = true → q < 144 := by
    intro q hq
    rw [tb_land, full_tb, Bool.and_eq_true, decide_eq_true_eq] at hq
    exact hq.2
  obtain ⟨h1, i, e', hi, he, ha, hb⟩ := hullC_spec _ hp q h
  rw [tb_land, Bool.and_eq_true] at ha hb
  exact ⟨h1, i, e', hi, he, ha.1, hb.1⟩

def tw : List ℕ → ℕ → ℕ → ℕ
  | [], _, t => t
  | a :: l, o, t => tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))

def priv (t a : ℕ) : ℕ := hull (Nat.land a (Nat.xor t full))

def hullsOK (t : ℕ) : List ℕ → ℕ → Bool
  | [], _ => true
  | a :: l, acc => Nat.beq (Nat.land (priv t a) a) (priv t a) &&
      (Nat.beq (Nat.land acc (priv t a)) 0 && hullsOK t l (Nat.lor acc (priv t a)))

def avOK1 (as : List ℕ) : Bool := hullsOK (tw as 0 0) as 0

def orL : List ℕ → ℕ
  | [] => 0
  | a :: l => Nat.lor a (orL l)

def rectOK1 (l : List ℕ) : Bool := avOK1 (l.map rectW)

def IsRect (R : ℕ → Prop) : Prop :=
  ∀ e i e' i' : ℕ, e < 12 → i < 12 → e' < 12 → i' < 12 →
    R (12 * e + i) → R (12 * e' + i') → R (12 * e + i')

def Part (zs : List ((ℕ → Prop) × ℕ)) : Prop :=
  (∀ z ∈ zs, IsRect z.1) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → q < 144) ∧
  (zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False)) ∧
  (∀ q, q < 144 → ∃ z ∈ zs, z.1 q) ∧
  (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true)

theorem Part.rect {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, IsRect z.1 := h.1

theorem Part.bnd {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q, z.1 q → q < 144 := h.2.1

theorem Part.disj {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) := h.2.2.1

theorem Part.cov {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ q, q < 144 → ∃ z ∈ zs, z.1 q := h.2.2.2.1

theorem Part.sub {zs : List ((ℕ → Prop) × ℕ)} (h : Part zs) :
    ∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true := h.2.2.2.2


theorem pw_forall {α : Type} {R : α → α → Prop} (hs : ∀ a b, R a b → R b a) :
    ∀ l : List α, l.Pairwise R → ∀ a ∈ l, ∀ b ∈ l, a ≠ b → R a b := by
  intro l
  induction l with
  | nil => intro _ a ha; simp at ha
  | cons x l ih =>
    intro h a ha b hb hab
    rw [List.pairwise_cons] at h
    rcases List.mem_cons.mp ha with ha' | ha'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · exact absurd (ha'.trans hb'.symm) hab
      · rw [ha']; exact h.1 b hb'
    · rcases List.mem_cons.mp hb with hb' | hb'
      · rw [hb']; exact hs _ _ (h.1 a ha')
      · exact ih h.2 a ha' b hb' hab

theorem tw_spec (q : ℕ) : ∀ (as : List ℕ) (o t : ℕ), (tw as o t).testBit q = false →
    t.testBit q = false ∧ (o.testBit q = true → ∀ a ∈ as, a.testBit q = false) ∧
    as.Pairwise (fun a b => ¬ (a.testBit q = true ∧ b.testBit q = true)) := by
  intro as
  induction as with
  | nil => intro o t h; exact ⟨h, fun _ a ha => by simp at ha, List.Pairwise.nil⟩
  | cons a l ih =>
    intro o t h
    obtain ⟨h1, h2, h3⟩ := ih (Nat.lor o a) (Nat.lor t (Nat.land o a)) h
    rw [tb_lor, Bool.or_eq_false_iff, tb_land] at h1
    refine ⟨h1.1, ?_, ?_⟩
    · intro ho b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · have h4 := h1.2
        rw [ho] at h4
        simpa using h4
      · exact h2 (by rw [tb_lor, ho]; rfl) b hb
    · refine List.pairwise_cons.mpr ⟨?_, h3⟩
      intro b hb hab
      have h4 := h2 (by rw [tb_lor, hab.1]; simp) b hb
      rw [h4] at hab
      exact Bool.noConfusion hab.2

theorem priv_in {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) : ∀ z ∈ zs, ∀ q,
    (priv (tw (zs.map Prod.snd) 0 0) z.2).testBit q = true → z.1 q := by
  intro z hz q hq
  obtain ⟨hq144, i, e', hi, he', ha, hb⟩ := hull_spec _ q hq
  have key : ∀ x, x < 144 →
      (Nat.land z.2 (Nat.xor (tw (zs.map Prod.snd) 0 0) full)).testBit x = true → z.1 x := by
    intro x hx hbit
    rw [tb_land, tb_xor, full_tb, Bool.and_eq_true] at hbit
    obtain ⟨hzx, ht⟩ := hbit
    have ht' : (tw (zs.map Prod.snd) 0 0).testBit x = false := by simpa [hx] using ht
    obtain ⟨_, _, hpw⟩ := tw_spec x _ 0 0 ht'
    rw [List.pairwise_map] at hpw
    obtain ⟨z', hz', hzq⟩ := hP.cov x hx
    by_cases hzz : z' = z
    · rw [← hzz]; exact hzq
    · exfalso
      exact pw_forall (fun a b h h' => h ⟨h'.2, h'.1⟩) zs hpw z' hz' z hz hzz
        ⟨hP.sub z' hz' x hzq, hzx⟩
  have h1 := key _ (by omega) ha
  have h2 := key _ (by omega) hb
  have h3 := hP.rect z hz (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
    h1 h2
  rwa [Nat.div_add_mod] at h3

theorem hullsOK_sound (t : ℕ) : ∀ (zs : List ((ℕ → Prop) × ℕ)) (acc : ℕ),
    (∀ z ∈ zs, ∀ q, (priv t z.2).testBit q = true → z.1 q) →
    (∀ z ∈ zs, ∀ q, z.1 q → z.2.testBit q = true) →
    zs.Pairwise (fun z z' => ∀ q, z.1 q → z'.1 q → False) →
    (∀ q, acc.testBit q = true → ∀ z ∈ zs, ¬ z.1 q) →
    hullsOK t (zs.map Prod.snd) acc = true := by
  intro zs
  induction zs with
  | nil => intros; rfl
  | cons z zs ih =>
    intro acc hh hs hd ha
    rw [List.pairwise_cons] at hd
    have hz := hh z List.mem_cons_self
    have e1 := land_sub _ _ (fun q hq => hs z List.mem_cons_self q (hz q hq))
    have e2 := land_disj acc (priv t z.2) (fun q h1 h2 => ha q h1 z List.mem_cons_self (hz q h2))
    have e3 := ih (Nat.lor acc (priv t z.2)) (fun z' hz' => hh z' (List.mem_cons_of_mem _ hz'))
      (fun z' hz' => hs z' (List.mem_cons_of_mem _ hz')) hd.2 (fun q hq z' hz' hz'q => by
        rw [tb_lor, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact ha q hq z' (List.mem_cons_of_mem _ hz') hz'q
        · exact hd.1 z' hz' q (hz q hq) hz'q)
    show (Nat.beq (Nat.land (priv t z.2) z.2) (priv t z.2) &&
      (Nat.beq (Nat.land acc (priv t z.2)) 0 &&
        hullsOK t (zs.map Prod.snd) (Nat.lor acc (priv t z.2)))) = true
    rw [e1, e2, e3, Nat.beq_refl]
    rfl

theorem avOK1_sound {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) :
    avOK1 (zs.map Prod.snd) = true :=
  hullsOK_sound _ zs 0 (priv_in hP) hP.sub hP.disj (fun q hq => by simp at hq)

end PackedRect

def witnessWord (w : (Nat × Nat × Nat)) : Nat := w.1

def essentialB (mask target : Nat) (stock : List Nat) (entry : (Nat × Nat × Nat)) : Bool :=
  let (w,p,n) := entry
  mask.testBit p && mask.testBit n && target.testBit p && !target.testBit n &&
    (w.testBit p != w.testBit n) &&
    stock.all (fun x => x == w || x.testBit p == x.testBit n)

theorem essentialRequired {stock : List Nat} {entry : (Nat × Nat × Nat)} {S : Finset Nat} {k t : Nat}
    (ok : essentialB mask target stock entry = true)
    (sub : ∀ w ∈ S, w ∈ stock) (live : LiveWord mask target k t S) :
    witnessWord entry ∈ S := by
  obtain ⟨w,p,n⟩ := entry
  simp only [essentialB, Bool.and_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨mp,mn⟩,tp⟩,tn⟩,unequal⟩,rest⟩ := ok
  by_contra no
  have all : ∀ x ∈ S, AgreesAt p n x := by
    intro x hx
    have h := List.all_eq_true.mp rest x (sub x hx)
    have hw : x ≠ w := fun e => no (by simpa [witnessWord, e] using hx)
    simpa [hw, AgreesAt] using h
  have agree := liveAgrees live (mp.trans mn.symm) all
  have falseBit : target.testBit n = false := by simpa using tn
  simp [AgreesAt, tp, falseBit] at agree

theorem essentialWordsIn {stock : List Nat} {witnesses : List (Nat × Nat × Nat)} {S : Finset Nat} {k t : Nat}
    (ok : witnesses.all (essentialB mask target stock) = true)
    (sub : ∀ w ∈ S, w ∈ stock) (live : LiveWord mask target k t S) :
    (witnesses.map witnessWord).toFinset ⊆ S := by
  intro w hw
  obtain ⟨entry, mem, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hw)
  exact essentialRequired (List.all_eq_true.mp ok entry mem) sub live

theorem essentialLower {stock : List Nat} {witnesses : List (Nat × Nat × Nat)} {minimum : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (bound : minimum ≤ (witnesses.map witnessWord).toFinset.card - 1) :
    Lower mask stock target minimum := by
  intro values build hit
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive masked build hit proper
  have card := Finset.card_le_card (essentialWordsIn ok sub live)
  have size := (liveWordSize live).2
  omega

theorem essentialLift {stock cutStock : List Nat} {witnesses : List (Nat × Nat × Nat)} {minimum cut prior : Nat}
    (proper : properWord mask target)
    (masked : ∀ w ∈ stock, Masked mask w)
    (ok : witnesses.all (essentialB mask target stock) = true)
    (submask : mask &&& cut = cut)
    (cutProper : properWord cut (target &&& cut))
    (supplies : ∀ w ∈ stock, AvailableWord cut cutStock (w &&& cut))
    (known : Lower cut cutStock (target &&& cut) prior)
    (bound : minimum ≤ prior + (flatSet cut (witnesses.map witnessWord).toFinset).card) :
    Lower mask stock target minimum := by
  intro values build hit
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive masked build hit proper
  have subW := essentialWordsIn ok sub live
  have subFlat : flatSet cut (witnesses.map witnessWord).toFinset ⊆ flatSet cut S :=
    Finset.filter_subset_filter _ subW
  have card := Finset.card_le_card subFlat
  have pf : ¬maskedFlat cut target := by simpa [maskedFlat, properWord] using cutProper
  obtain ⟨n, budget, built⟩ := maskedBuild live cut submask pf
  have starts : ∀ w ∈ projectedStock cut S, AvailableWord cut cutStock w := by
    intro w hw
    simp only [projectedStock, visibleWords, Finset.mem_insert, Finset.mem_image] at hw
    rcases hw with rfl | rfl | ⟨x,hx,rfl⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact supplies _ (sub _ hx)
  obtain ⟨ys,len,built',out⟩ := buildableWords built starts
  have lower := known ys built' out
  omega

def unpackWitnesses (stock : List Nat) (codes : List Nat) : List (Nat × Nat × Nat) :=
  List.rec [] (fun code _ rest =>
    (stock.getD (code >>> 18) 0, (code >>> 9) &&& 511, code &&& 511) :: rest) codes

def DagAuto (mask goal : Nat) (select : Fin rows → Fin rows) : Prop :=
  Function.Surjective select ∧ relabel select mask = mask ∧ relabel select goal = goal


def mixStep (m : (List (Nat × Nat) × List (Nat × Nat))) (w : Nat) : Nat :=
  let left := List.rec 0 (fun (part,n) _ acc => ((w &&& part) <<< n) ||| acc) m.1
  let right := List.rec 0 (fun (part,n) _ acc => ((w &&& part) >>> n) ||| acc) m.2
  left ||| right

def BitLinear (f : Nat → Nat) : Prop :=
  ∀ w i, (f w).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (2 ^ j)).testBit i = true

theorem bitLinearZero : BitLinear (fun _ => 0) := by
  simp [BitLinear]

theorem bitLinearOr {f g : Nat → Nat} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f w ||| g w) := by
  intro w i
  change ((f w ||| g w).testBit i = true) ↔ _
  simp only [Nat.testBit_or, Bool.or_eq_true]
  rw [hf w i, hg w i]
  constructor
  · rintro (⟨j,hw,hj⟩ | ⟨j,hw,hj⟩)
    · exact ⟨j,hw,Or.inl hj⟩
    · exact ⟨j,hw,Or.inr hj⟩
  · rintro ⟨j,hw,hj | hj⟩
    · exact Or.inl ⟨j,hw,hj⟩
    · exact Or.inr ⟨j,hw,hj⟩

theorem bitLinearLeft (mask n : Nat) : BitLinear (fun w => (w &&& mask) <<< n) := by
  intro w i
  simp only [Nat.testBit_shiftLeft, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨h, hw, hm⟩
    exact ⟨i-n,hw,h,rfl,hm⟩
  · rintro ⟨j,hw,h,rfl,hm⟩
    exact ⟨h,hw,hm⟩

theorem bitLinearRight (mask n : Nat) : BitLinear (fun w => (w &&& mask) >>> n) := by
  intro w i
  simp only [Nat.testBit_shiftRight, Nat.testBit_and, Nat.testBit_two_pow,
    Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hw,hm⟩
    exact ⟨n+i,hw,rfl,hm⟩
  · rintro ⟨j,hw,rfl,hm⟩
    exact ⟨hw,hm⟩

theorem mixStepLinear (move : (List (Nat × Nat) × List (Nat × Nat))) : BitLinear (mixStep move) := by
  obtain ⟨left, right⟩ := move
  unfold mixStep
  apply bitLinearOr
  · induction left with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearLeft part count) ih
  · induction right with
    | nil => exact bitLinearZero
    | cons entry rest ih =>
      obtain ⟨part, count⟩ := entry
      exact bitLinearOr (bitLinearRight part count) ih

def mixMove (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (w : Nat) : Nat :=
  (List.rec (motive := fun _ => Nat → Nat) id
    (fun step _ next w => next (mixStep step w)) move) w

theorem bitLinearId : BitLinear id := by
  intro w i
  change w.testBit i = true ↔ ∃ j, w.testBit j = true ∧ (2 ^ j).testBit i = true
  simp [Nat.testBit_two_pow]

theorem bitLinearComp {f g : Nat → Nat} (hf : BitLinear f) (hg : BitLinear g) :
    BitLinear (fun w => f (g w)) := by
  intro w i
  change (f (g w)).testBit i = true ↔ ∃ j, w.testBit j = true ∧ (f (g (2 ^ j))).testBit i = true
  rw [hf]
  constructor
  · rintro ⟨j,gj,fj⟩
    obtain ⟨k,wk,gk⟩ := (hg w j).mp gj
    exact ⟨k,wk,(hf (g (2^k)) i).mpr ⟨j,gk,fj⟩⟩
  · rintro ⟨j,wj,h⟩
    obtain ⟨k,gk,fk⟩ := (hf (g (2^j)) i).mp h
    exact ⟨k,(hg w k).mpr ⟨j,wj,gk⟩,fk⟩

theorem mixMoveLinear (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : BitLinear (mixMove move) := by
  induction move with
  | nil => exact bitLinearId
  | cons op ops ih =>
    change BitLinear (fun w => mixMove ops (mixStep op w))
    exact bitLinearComp ih (mixStepLinear op)

def permuteAxes (axes : List Nat) (offset row : Nat) : Nat :=
  offset ^^^ (List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun j _ next i => (if row.testBit i then 1 <<< j else 0) ||| next (i + 1)) axes) 0

theorem relabelLinear (select : Fin rows → Fin rows) : BitLinear (relabel select) := by
  intro w i
  by_cases inside : i < rows
  · let ii : Fin rows := ⟨i,inside⟩
    change (relabel select w).testBit ii.val = true ↔ _
    rw [relabelBit]
    constructor
    · intro h
      refine ⟨(select ii).val,h,?_⟩
      change (relabel select (2 ^ (select ii).val)).testBit ii.val = true
      rw [relabelBit, Nat.testBit_two_pow]
      simp
    · rintro ⟨j,h,bit⟩
      change (relabel select (2^j)).testBit ii.val = true at bit
      rw [relabelBit, Nat.testBit_two_pow, decide_eq_true_eq] at bit
      exact bit ▸ h
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]
    simp [relabelOutside _ _ _ (Nat.le_of_not_gt inside)]

theorem wordMoveAgreement {select : Fin rows → Fin rows} {mask : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))}
    (bounded : Masked (fullMask rows) mask)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = relabel select (2 ^ i.val))
    {w : Nat} (masked : Masked mask w) : mixMove move w = relabel select w := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [mixMoveLinear, relabelLinear]
  have source {j : Nat} (bit : w.testBit j = true) :
      mixMove move (2^j) = relabel select (2^j) := by
    have m : mask.testBit j = true := by
      have eq := congrArg (fun x : Nat => x.testBit j) masked
      simpa [Nat.testBit_and, bit] using eq
    have within : j < rows := by
      have eq := congrArg (fun x : Nat => x.testBit j) bounded
      simpa [Nat.testBit_and, fullMask, Nat.testBit_two_pow_sub_one, m] using eq
    exact basis ⟨j,within⟩ m
  constructor <;> rintro ⟨j,hj,hi⟩
  · exact ⟨j,hj,by rwa [← source hj]⟩
  · exact ⟨j,hj,by rwa [source hj]⟩

theorem relabelBasis {select inverse : Fin rows → Fin rows}
    (left : ∀ i, inverse (select i) = i) :
    ∀ j : Fin rows, select (inverse j) = j →
      relabel select (2 ^ j.val) = 2 ^ (inverse j).val := by
  intro j right
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases inside : i < rows
  · let pos : Fin rows := ⟨i,inside⟩
    change (relabel select (2 ^ j.val)).testBit pos.val = _
    rw [relabelBit, Nat.testBit_two_pow, Nat.testBit_two_pow]
    apply (Bool.eq_iff_iff).mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro eq
      have e : j = select pos := Fin.ext eq
      rw [e,left]
    · intro eq
      have hp : inverse j = pos := Fin.ext eq
      rw [← hp, right]
  · rw [relabelOutside _ _ _ (Nat.le_of_not_gt inside), Nat.testBit_two_pow]
    have ne : (inverse j).val ≠ i := by have := (inverse j).isLt; omega
    simp [ne]

theorem dagAutoFromMove {select inverse : Fin rows → Fin rows} {mask goal : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))}
    (left : ∀ i, inverse (select i) = i)
    (right : ∀ i, select (inverse i) = i)
    (bm : Masked (fullMask rows) mask)
    (gm : Masked mask goal)
    (basis : ∀ i : Fin rows, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val)
    (sameMask : mixMove move mask = mask) (sameGoal : mixMove move goal = goal) :
    DagAuto mask goal select ∧ ∀ w, Masked mask w → mixMove move w = relabel select w := by
  have agree {w : Nat} (hw : Masked mask w) : mixMove move w = relabel select w :=
    wordMoveAgreement bm (fun i h => (basis i h).trans (relabelBasis left i (right i)).symm) hw
  exact ⟨⟨fun i => ⟨inverse i,right i⟩,(agree (by simp [Masked])).symm.trans sameMask,
    (agree gm).symm.trans sameGoal⟩,fun _ h => agree h⟩

theorem maskedBelow {mask w : Nat} (bm : Masked (fullMask rows) mask)
    (bw : Masked mask w) : Masked (fullMask rows) w := by
  unfold Masked at *
  rw [← bw, Nat.land_assoc, bm, bw]

theorem maskedTransfer {mask w : Nat} {select : Fin rows → Fin rows}
    (same : relabel select mask = mask) (hw : Masked mask w) :
    Masked mask (relabel select w) := by
  unfold Masked at *
  rw [← same, ← relabelAnd, hw]

theorem liveMaskedImage {mask goal : Nat} {select : Fin rows → Fin rows}
    (auto : DagAuto mask goal select) (maskBounds : Masked (fullMask rows) mask)
    {k t : Nat} {S : Finset Nat} (live : LiveWord mask goal k t S)
    (masked : ∀ w ∈ S, Masked mask w) :
    LiveWord mask goal k t (S.image (relabel select)) := by
  let f := relabel select
  have hmask : f mask = mask := auto.2.1
  have inj {a b : Nat} (ma : Masked mask a) (mb : Masked mask b) :
      f a = f b → a = b :=
    relabelInj select auto.1 (maskedBelow maskBounds ma) (maskedBelow maskBounds mb)
  have proper {a : Nat} (ma : Masked mask a) (ha : properWord mask a) :
      properWord mask (f a) := by
    exact ⟨fun eq => ha.1 (inj ma (by simp [Masked]) (eq.trans (relabelZero select).symm)),
      fun eq => ha.2 (inj ma (by simp [Masked]) (eq.trans hmask.symm))⟩
  have freshImage {S : Finset Nat} {v : Nat} (hv : v ∉ S) (mv : Masked mask v)
      (ms : ∀ w ∈ S, Masked mask w) : f v ∉ S.image f := by
    intro hw
    obtain ⟨w,hs,eq⟩ := Finset.mem_image.mp hw
    exact hv (inj (ms w hs) mv eq ▸ hs)
  induction live using LiveWord.ind with
  | stop hp =>
    rw [Finset.image_singleton, auto.2.2]
    exact LiveWord.stop hp
  | @unary k t U a ha fresh tail ih =>
    let v := mask ^^^ a
    have ma := masked a (Finset.mem_insert_self ..)
    have mv : Masked mask v := by
      apply maskedGate (bank := [a]) (by simpa using ma)
      exact Or.inl ⟨a, Or.inr (Or.inr (by simp)), rfl⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem hU)
    have fve : f v = mask ^^^ f a := by
      change relabel select (mask ^^^ a) = _
      rw [relabelXor, auto.2.1]
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) (t+1) ((insert a U).image f)
    rw [Finset.image_insert] at ht hf
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht hf
    rw [Finset.image_insert]
    exact LiveWord.unary (proper ma ha) hf ht
  | @binary k t U a b op pa pb ab fresh tail ih =>
    let v := binWord op a b
    have ma := masked a (Finset.mem_insert_self ..)
    have mb := masked b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have mv : Masked mask v := by
      apply maskedGate (bank := [a,b]) (by simpa using And.intro ma mb)
      exact Or.inr ⟨a,b,Or.inr (Or.inr (by simp)),Or.inr (Or.inr (by simp)),by
        cases op <;> simp [v, binWord]⟩
    have hnew : ∀ w ∈ insert v U, Masked mask w := by
      intro w h
      rcases Finset.mem_insert.mp h with rfl | hU
      · exact mv
      · exact masked _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have fve : f v = binWord op (f a) (f b) := by
      cases op
      · exact relabelAnd ..
      · exact relabelOr ..
    have ht := ih hnew
    have hf := freshImage fresh mv masked
    change LiveWord mask goal (k+1) t ((insert a (insert b U)).image f)
    rw [Finset.image_insert] at ht
    change LiveWord mask goal k t (insert (f v) (U.image f)) at ht
    rw [fve] at ht
    rw [Finset.image_insert, Finset.image_insert, fve] at hf
    rw [Finset.image_insert, Finset.image_insert]
    exact LiveWord.binary (proper ma pa) (proper mb pb) (fun h => ab (inj ma mb h)) hf ht

def dagMoveWords (m : (List (List (Nat × Nat) × List (Nat × Nat)))) (ws : List Nat) : List Nat :=
  List.rec [] (fun w _ next => insertWord (mixMove m w) next) ws

theorem dagMoveSet {m : (List (List (Nat × Nat) × List (Nat × Nat)))} {ws : List Nat} {select : Fin rows → Fin rows}
    (agree : ∀ w ∈ ws, mixMove m w = relabel select w) :
    (dagMoveWords m ws).toFinset = ws.toFinset.image (relabel select) := by
  induction ws with
  | nil => simp [dagMoveWords]
  | cons w ws ih =>
    change (insertWord (mixMove m w) (dagMoveWords m ws)).toFinset = _
    rw [insertWordSet, ih (fun w hw => agree _ (List.mem_cons_of_mem _ hw)),
      agree _ List.mem_cons_self, List.toFinset_cons, Finset.image_insert]

def chartRow (chart : ({ rows : List Nat // rows.length = 24 })) (i : Nat) : Nat :=
  chart.val.getD i 0

def chartBits (w : Nat) (rows : List Nat) : Nat :=
  List.rec 0 (fun r _ packed => ((w >>> r) &&& 1) ||| (packed <<< 1)) rows

theorem chartBitsBit (w : Nat) (rows : List Nat) (i : Nat) (hi : i < rows.length) :
    (chartBits w rows).testBit i = w.testBit (rows.getD i 0) := by
  induction rows generalizing i with
  | nil => simp at hi
  | cons row rows ih =>
    change (((w >>> row) &&& 1) ||| (chartBits w rows <<< 1)).testBit i = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have lt : i < rows.length := by simpa using hi
      simp [ih i lt, Nat.testBit_succ]

def chartWord (chart : ({ rows : List Nat // rows.length = 24 })) (w : Nat) : Nat := chartBits w chart.val

def ChartOK (goal : Nat) (chart : ({ rows : List Nat // rows.length = 24 })) : Prop :=
  (∀ i : Fin 12, goal.testBit (chartRow chart i.val) = true) ∧
  (∀ i : Fin 12, goal.testBit (chartRow chart (12+i.val)) = false)

def chartCheck (goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) : Bool :=
  chart.all fun c => @decide (ChartOK goal c) (by unfold ChartOK; infer_instance)

theorem chartOfCheck {goal : Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    (ok : chartCheck goal chart = true) (c : ({ rows : List Nat // rows.length = 24 })) (eq : chart = some c) :
    ChartOK goal c := by
  subst chart
  unfold ChartOK
  exact of_decide_eq_true ok

theorem chartWordBit (chart : ({ rows : List Nat // rows.length = 24 })) (w : Nat) {i : Nat} (hi : i < 24) :
    (chartWord chart w).testBit i = w.testBit (chartRow chart i) := by
  exact chartBitsBit w chart.val i (by rw [chart.property]; exact hi)

theorem chartPos {goal : Nat} {chart : ({ rows : List Nat // rows.length = 24 })} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart i) = true := ok.1 ⟨i,hi⟩

theorem chartNeg {goal : Nat} {chart : ({ rows : List Nat // rows.length = 24 })} (ok : ChartOK goal chart) {i : Nat} (hi : i < 12) :
    goal.testBit (chartRow chart (12+i)) = false := ok.2 ⟨i,hi⟩

theorem chartRectangles {goal : Nat} {chart : ({ rows : List Nat // rows.length = 24 })} {ws : List Nat}
    (ok : ChartOK goal chart) (nd : ws.Nodup) (kw : KWPartition goal ws.toFinset) :
    PackedRect.rectOK1 (ws.map (chartWord chart)) = true := by
  obtain ⟨f, good, rectangle⟩ := kw
  let label := fun p n => f (chartRow chart p) (chartRow chart (12+n))
  let part := fun w => ((fun q : Nat => q < 144 ∧ label (q/12) (q % 12) = w),
    PackedRect.rectW (chartWord chart w))
  have partition : PackedRect.Part (ws.map part) := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro z hz
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      intro p n p' n' hp hn hp' hn' h h'
      have divmod (a b : Nat) (lt : b < 12) :
          (12*a+b)/12 = a ∧ (12*a+b)%12 = b := by omega
      have h1 := h.2
      have h2 := h'.2
      rw [(divmod p n hn).1, (divmod p n hn).2] at h1
      rw [(divmod p' n' hn').1, (divmod p' n' hn').2] at h2
      refine ⟨by omega,?_⟩
      rw [(divmod p n' hn').1, (divmod p n' hn').2]
      exact (rectangle _ _ _ _ (chartPos ok hp) (chartPos ok hp') (chartNeg ok hn)
        (chartNeg ok hn') (h1.trans h2.symm)).trans h1
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      exact hq.1
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun hne q h1 h2 => hne (h1.2.symm.trans h2.2)) nd
    · intro q hq
      have member := (good _ _ (chartPos ok (show q/12 < 12 by omega))
        (chartNeg ok (Nat.mod_lt q (by decide : 0 < 12)))).1
      exact ⟨_, List.mem_map.mpr ⟨_,List.mem_toFinset.mp member,rfl⟩,hq,rfl⟩
    · intro z hz q hq
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hz
      obtain ⟨bound, same⟩ := hq
      have hp : q/12 < 12 := by omega
      have hn : q % 12 < 12 := Nat.mod_lt _ (by decide)
      have h := (good _ _ (chartPos ok hp) (chartNeg ok hn)).2
      change (label (q/12) (q % 12)).testBit (chartRow chart (q/12)) = true ∧
        (label (q/12) (q % 12)).testBit (chartRow chart (12+q % 12)) = false at h
      rw [same] at h
      have bit := PackedRect.rectW_tb (chartWord chart w) (q/12) (q % 12) hp hn
        ((chartWordBit chart w (by omega)).trans h.1)
        ((chartWordBit chart w (by omega)).trans h.2)
      rwa [Nat.div_add_mod] at bit
  have hw := PackedRect.avOK1_sound partition
  simpa only [PackedRect.rectOK1, List.map_map, Function.comp_def, part] using hw

theorem tightChart {goal mask : Nat} {chart : ({ rows : List Nat // rows.length = 24 })} {ws : List Nat} {fuel : Nat}
    (ok : ChartOK goal chart) (tight : ws.length = fuel + 1)
    (viable : WordViable mask goal (fuel,ws,[])) : PackedRect.rectOK1 (ws.map (chartWord chart)) = true := by
  obtain ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel at cap
  have card := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at card
  change (ws : List Nat).length + t ≤ k + 1 at card
  have ht : t = 0 := by omega
  have hk : ws.toFinset.card = k + 1 := by
    have q : ws.toFinset.card = ws.length := List.toFinset_card_of_nodup nd
    omega
  subst t
  exact chartRectangles ok nd (kwFromLive live hk)

def dagForceWord {α : Type} (word : Nat) (cont : Nat → α) : α :=
  Nat.rec (cont 0) (fun k _ => cont (k + 1)) word

theorem dagForceWordEq {α : Type} (word : Nat) (cont : Nat → α) :
    dagForceWord word cont = cont word := by cases word <;> rfl

def dagForceWords (words : List Nat) (cont : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => dagForceWord w (fun v => next (fun rest => k (v :: rest)))) words) cont

theorem dagForceWordsEq (words : List Nat) (cont : List Nat → Bool) :
    dagForceWords words cont = cont words := by
  induction words generalizing cont with
  | nil => rfl
  | cons w ws ih =>
    change dagForceWord w (fun v => dagForceWords ws (fun rest => cont (v :: rest))) = _
    rw [dagForceWordEq, ih]

def dagBoundCloses (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (bound : (Nat × List Nat × Nat × Nat)) : Bool :=
  let (mask, stock, lower, goal) := bound
  let (fuel, ws, history) := state
  (target &&& mask) == goal && goal != 0 && goal != mask &&
    dagForceWord (fuel - flatCount mask ws) (fun remaining =>
      if Nat.blt remaining lower then
        dagForceWords (recipeStart mask stock ws) (fun start =>
          if Nat.blt (start.length + remaining) lower then
            dagForceWords (recipeClosure mask stock history start) (fun needed =>
              if Nat.blt (needed.length + remaining) lower then
                dagForceWords (replayRecipes mask needed history.reverse stock) (fun replay =>
                  decide (replay.length + remaining < lower) &&
                    ws.all (fun w => availableB mask (replay ++ stock) (w &&& mask)))
              else false)
          else false)
      else false)

theorem dagBoundClosesEq (target : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (bound : (Nat × List Nat × Nat × Nat)) :
    dagBoundCloses target state bound = boundCloses target state bound := by
  obtain ⟨fuel, ws, history⟩ := state
  obtain ⟨mask, stock, lower, goal⟩ := bound
  simp [dagBoundCloses, boundCloses, dagForceWordsEq, dagForceWordEq, Nat.blt_eq]

def dagKnownCloses (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  List.rec false (fun bound _ later => dagBoundCloses target state bound || later) bounds

theorem dagKnownClosesEq (target : Nat) (bounds : List (Nat × List Nat × Nat × Nat)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) :
    dagKnownCloses target bounds state = knownCloses target bounds state := by
  induction bounds with
  | nil => rfl
  | cons bound bounds ih =>
    change (dagBoundCloses target state bound || dagKnownCloses target bounds state) =
      (boundCloses target state bound || knownCloses target bounds state)
    rw [dagBoundClosesEq, ih]


def dagAllowedRoot (witnesses : List (Nat × Nat × Nat)) (ws : List Nat) : Bool :=
  witnesses.all (fun entry => ws.contains (witnessWord entry))

def dagTrace (mask : Nat) (stock : List Nat) (fuel : Nat) (forest : (Nat → Nat × Nat))
    (i : Nat) : Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (Nat.rec (motive := fun _ => Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (fun _ => none)
    (fun _ previous j =>
      let (parent, token) := forest j
      if parent == 0 then
        if token < 2 ^ stock.length then some (rootState stock fuel token) else none
      else (previous (parent - 1)).bind (childState mask token)) (fuel + 1)) i

def dagRef (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat)))
    (moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))) (links : (Nat → Nat → Option (Nat × Nat))) (parent token : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  match links parent token with
  | none => false
  | some (destination, auto) =>
    Nat.blt destination count &&
      match states destination with
      | none => false
      | some saved =>
        saved.1 == state.1 &&
          if auto == 0 then saved.2.1 == state.2.1
          else match moves[auto-1]? with
               | none => false
               | some m => saved.2.1 == dagMoveWords m state.2.1

def dagPartition (directed : Bool) (ws : List Nat) : Nat → Nat → Bool :=
  List.rec
    (fun p n => Nat.beq p 0 || Nat.beq n 0)
    (fun w _ rest p n =>
      Nat.beq p 0 || Nat.beq n 0 ||
      dagForceWord (p &&& w) (fun up =>
        dagForceWord (n &&& w) (fun down =>
          rest up down &&
            dagForceWord (p ^^^ up) (fun offP =>
              dagForceWord (if directed then n else n ^^^ down) (rest offP))))) ws

theorem dagOffBits {v w : Nat} {i : Nat} (bit : (v ^^^ (v &&& w)).testBit i = true) :
    v.testBit i = true ∧ w.testBit i = false := by
  rw [Nat.testBit_xor, Nat.testBit_and] at bit
  cases hv : v.testBit i <;> cases hw : w.testBit i <;> simp [hv, hw] at bit ⊢

theorem dagPartitionSound {directed : Bool} {ws : List Nat} {positive negative : Nat}
    (fail : dagPartition directed ws positive negative = false) :
    ∃ p n, positive.testBit p = true ∧ negative.testBit n = true ∧
      ∀ w ∈ ws, if directed then w.testBit p = true → w.testBit n = true
                  else w.testBit p = w.testBit n := by
  have nonempty {w : Nat} (hn : w ≠ 0) : ∃ j, w.testBit j = true := by
    by_contra! all
    apply hn
    apply Nat.eq_of_testBit_eq
    intro i
    simp [all i]
  induction ws generalizing positive negative with
  | nil =>
    change (Nat.beq positive 0 || Nat.beq negative 0) = false at fail
    simp only [Bool.or_eq_false_iff] at fail
    obtain ⟨p,hp⟩ := nonempty (w := positive) (fun eq => by simp [eq] at fail)
    obtain ⟨n,hn⟩ := nonempty (w := negative) (fun eq => by simp [eq] at fail)
    exact ⟨p,n,hp,hn,by simp⟩
  | cons w ws ih =>
    change (Nat.beq positive 0 || Nat.beq negative 0 ||
      dagForceWord (positive &&& w) (fun up =>
        dagForceWord (negative &&& w) (fun down =>
          dagPartition directed ws up down &&
            dagForceWord (positive ^^^ up) (fun offP =>
              dagForceWord (if directed then negative else negative ^^^ down)
                (dagPartition directed ws offP))))) = false at fail
    simp only [dagForceWordEq, Bool.or_eq_false_iff, Bool.and_eq_false_iff] at fail
    rcases fail.2 with on | off
    · obtain ⟨p,n,hp,hn,agree⟩ := ih on
      rw [Nat.testBit_and, Bool.and_eq_true] at hp hn
      refine ⟨p,n,hp.1,hn.1,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | tail
      · simp [hp.2, hn.2]
      · exact agree _ tail
    · obtain ⟨p,n,hp,hn,agree⟩ := ih off
      have hp' := dagOffBits hp
      cases mode : directed
      · have hn' : negative.testBit n = true ∧ w.testBit n = false := by
          apply dagOffBits
          simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn'.1,?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2, hn'.2]
        · simpa [mode] using agree _ tail
      · have hn' : negative.testBit n = true := by simpa [mode] using hn
        refine ⟨p,n,hp'.1,hn',?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | tail
        · simp [hp'.2]
        · simpa [mode] using agree _ tail

theorem dagPartitionLive {mask goal : Nat} {ws : List Nat} {k t : Nat} {directed : Bool}
    (goalMask : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) :
    dagPartition directed ws goal (mask ^^^ goal) = true := by
  by_contra fail
  have openPair : dagPartition directed ws goal (mask ^^^ goal) = false := by
    cases h : dagPartition directed ws goal (mask ^^^ goal) <;> simp_all
  obtain ⟨p,n,hp,hn,agree⟩ := dagPartitionSound openPair
  have pm := positiveInMask goalMask hp
  have nm : mask.testBit n = true ∧ goal.testBit n = false := by
    rw [Nat.testBit_xor] at hn
    have implied := fun ht : goal.testBit n = true => positiveInMask goalMask ht
    cases hm : mask.testBit n <;> cases ht : goal.testBit n <;> simp_all
  cases mode : directed with
  | false =>
    have same := liveAgrees live (pm.trans nm.1.symm) (fun w hw => by
      simpa [mode,AgreesAt] using agree w (List.mem_toFinset.mp hw))
    simp [AgreesAt, hp, nm.2] at same
  | true =>
    have ht := noNot mode
    subst t
    obtain ⟨w,hw,a,b⟩ := liveDirected live hp nm.2
    have same := agree w (List.mem_toFinset.mp hw)
    simp [mode, a, b] at same


def dagForceCache (tags : List (Nat × Nat)) (use : List (Nat × Nat) → Bool) : Bool :=
  (List.rec (motive := fun _ => (List (Nat × Nat) → Bool) → Bool) (fun k => k [])
    (fun tag _ next k =>
      dagForceWord tag.1 (fun up => dagForceWord tag.2 (fun down =>
        next (fun tail => k ((up,down)::tail))))) tags) use

theorem dagForceCacheEq (tags : List (Nat × Nat)) (use : List (Nat × Nat) → Bool) :
    dagForceCache tags use = use tags := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag rest ih =>
    obtain ⟨a,b⟩ := tag
    change dagForceWord a (fun up => dagForceWord b (fun down =>
      dagForceCache rest (fun tail => use ((up,down)::tail)))) = _
    simp only [dagForceWordEq, ih]

def dagSignalContrast (directed : Bool) (full : Nat) (tag : (Nat × Nat)) : Nat :=
  if directed then tag.1 &&& (tag.2 ^^^ full) else tag.1 ^^^ tag.2

def dagCountStep (acc : (Nat × Nat × Nat)) (column : Nat) : (Nat × Nat × Nat) :=
  (acc.1 ||| column, acc.2.1 ||| (acc.1 &&& column), acc.2.2 ||| (acc.2.1 &&& column))

def dagCountSigns (directed : Bool) (full : Nat) (tags : List (Nat × Nat))
    (use : (Nat × Nat × Nat) → Bool) : Bool :=
  (List.rec (motive := fun _ => ((Nat × Nat × Nat) → Bool) → Bool) (fun k => k (0,0,0))
    (fun tag _ more k =>
      dagForceWord (dagSignalContrast directed full tag) (fun column =>
        more (fun acc =>
          dagForceWord (acc.1 ||| column) (fun once =>
            dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
              dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => k (once,twice,thrice)))))))
    tags) use

theorem dagCountSignsEq (directed : Bool) (full : Nat) (tags : List (Nat × Nat))
    (use : (Nat × Nat × Nat) → Bool) : dagCountSigns directed full tags use =
    use (tags.foldr (fun tag acc => dagCountStep acc (dagSignalContrast directed full tag)) (0,0,0)) := by
  induction tags generalizing use with
  | nil => rfl
  | cons tag tags ih =>
    change dagForceWord (dagSignalContrast directed full tag) (fun column =>
      dagCountSigns directed full tags (fun acc =>
        dagForceWord (acc.1 ||| column) (fun once =>
          dagForceWord (acc.2.1 ||| (acc.1 &&& column)) (fun twice =>
            dagForceWord (acc.2.2 ||| (acc.2.1 &&& column)) (fun thrice => use (once,twice,thrice)))))) = _
    simp only [dagForceWordEq, ih]
    rfl

def dagHighest (value : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ offset => offset)
    (fun i next w offset =>
      let shift := 1 <<< i
      dagForceWord (w >>> shift) (fun upper =>
        if Nat.beq upper 0 then next w offset else next upper (offset+shift))) 8) value 0

def dagSampleMiss (sample : (Nat × Nat)) (full : Nat) (normal tight : (Nat × Nat × Nat))
    (x y out : (Nat × Nat)) (directed : Bool) (op keep : Nat) : List Nat :=
  let counts := if directed then tight else normal
  let dx := if keep.testBit 0 then 0 else dagSignalContrast directed full x
  let dy := if op == 2 || keep.testBit 1 then 0 else dagSignalContrast directed full y
  let rest := counts.2.2 ||| (counts.2.1 ^^^ (counts.2.1 &&& dx &&& dy)) |||
    (counts.1 ^^^ (counts.1 &&& (dx ||| dy)))
  dagForceWord ((rest ||| dagSignalContrast directed full out) ^^^ full) (fun missing =>
    if Nat.beq missing 0 then [] else [unpack sample.1 18 (dagHighest missing)])

def dagPairReject (mask goal : Nat) (directed : Bool) (ws : List Nat) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    let p := code &&& 511
    let n := code >>> 9
    goal.testBit p && mask.testBit n && !goal.testBit n &&
      ws.all (fun w => if directed then !(w.testBit p) || w.testBit n
                       else w.testBit p == w.testBit n)

theorem dagPairsOpen {mask goal : Nat} {ws : List Nat} {pairs : List Nat} {k t : Nat} {directed : Bool}
    (masked : Masked mask goal) (live : LiveWord mask goal k t ws.toFinset)
    (noNot : directed = true → t = 0) : dagPairReject mask goal directed ws pairs = false := by
  apply Bool.eq_false_iff.mpr
  intro close
  obtain ⟨code,_,check⟩ := List.any_eq_true.mp close
  simp only [Bool.and_eq_true, Bool.not_eq_true, List.all_eq_true] at check
  obtain ⟨⟨⟨hp, mn⟩, hn⟩, bank⟩ := check
  have neg : goal.testBit (code >>> 9) = false := by simpa using hn
  cases mode : directed
  · have h := liveAgrees live ((positiveInMask masked hp).trans mn.symm) (fun w hw => by
      have pair := bank _ (List.mem_toFinset.mp hw)
      simpa [mode, AgreesAt] using pair)
    simp [AgreesAt, hp, neg] at h
  · have ht := noNot mode
    subst t
    obtain ⟨word,mem,on,off⟩ := liveDirected live hp neg
    have pair := bank _ (List.mem_toFinset.mp mem)
    simp [mode,on,off] at pair

def dagLocal (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 }))
    (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  let (fuel,ws,_) := state
  ws.length > fuel + 1 ||
    (!ws.contains goal &&
      (fuel == 0 ||
        (if ws.length == fuel + 1 then
           chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c)))
         else false) ||
        cut state ||
        (if ws.length == fuel + 1 then !dagPartition true ws goal (mask ^^^ goal)
         else !dagPartition false ws goal (mask ^^^ goal))))

def dagSizeFloor (n op keep : Nat) : Nat :=
  (n - (if keep.testBit 0 then 0 else 1) -
    (if op == 2 || keep.testBit 1 then 0 else 1)) + 1

def dagTooWide (n fuel token : Nat) : Bool :=
  dagSizeFloor n (token / 4 % 3) (token % 4) > (fuel-1) + 1

def dagKept (ws : List Nat) (op keep x y : Nat) : List Nat :=
  keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)

def dagGateWord (mask op x y : Nat) : Nat :=
  if Nat.beq op 0 then x &&& y else if Nat.beq op 1 then x ||| y else mask ^^^ x

def dagDirectChild (mask : Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (a b op keep x y out : Nat) : Option (Nat × List Nat × List (Nat × Nat × Nat)) :=
  let (fuel, ws, history) := state
  if fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b) then none
  else if out == 0 || out == mask || ws.contains out then none
  else
    some (fuel-1, insertWord out (dagKept ws op keep x y), (out,x,y) :: history)

theorem dagDirectChildEq {mask a b op keep : Nat} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (hb : b < 64) (hop : op < 3) (hk : keep < 4) :
    let x := state.2.1.getD a 0
    let y := state.2.1.getD b 0
    dagDirectChild mask state a b op keep x y (dagGateWord mask op x y) =
      childState mask (gateToken a b op keep) state := by
  obtain ⟨fuel,ws,history⟩ := state
  obtain ⟨keepEq,opEq,aEq,bEq⟩ := gateTokenFields (a := a) hb hop hk
  simp only [childState, keepEq, opEq, aEq, bEq]
  rfl


def dagTagBases (stock : List Nat) (positive negative width : Nat) : List (Nat × (Nat × Nat)) :=
  (List.rec (motive := fun _ => Nat → List (Nat × (Nat × Nat))) (fun _ => [])
    (fun w _ next i => (w, unpack positive width i, unpack negative width i) :: next (i+1)) stock) 0

def dagTagRoot (bank : List (Nat × (Nat × Nat))) (token : Nat) : List (Nat × (Nat × Nat)) :=
  (List.rec (motive := fun _ => Nat → List (Nat × (Nat × Nat))) (fun _ => [])
    (fun tag _ next k =>
      if Nat.beq (k &&& 1) 0 then next (k >>> 1) else tag :: next (k >>> 1)) bank) token

def dagTagKeep (keep : Bool) (w : Nat) (bank : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  if keep then bank
  else List.rec [] (fun tag tail next => if Nat.beq tag.1 w then tail else tag :: next) bank

def dagTagInsert (tag : (Nat × (Nat × Nat))) (bank : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  List.rec [tag] (fun old tail next => if Nat.ble tag.1 old.1 then tag :: old :: tail else old :: next) bank

def dagTagStep (mask full token : Nat) (bank : List (Nat × (Nat × Nat))) : List (Nat × (Nat × Nat)) :=
  let keep := token % 4
  let op := token / 4 % 3
  let x := bank.getD (token / (4*3*64)) (0,0,0)
  let y := bank.getD (token / (4*3) % 64) (0,0,0)
  let tag := (dagGateWord mask op x.1 y.1, dagGateWord full op x.2.1 y.2.1, dagGateWord full op x.2.2 y.2.2)
  dagTagInsert tag (dagTagKeep (op == 2 || keep.testBit 1) y.1 (dagTagKeep (keep.testBit 0) x.1 bank))

def dagTraceTags (mask width : Nat) (root : List (Nat × (Nat × Nat))) (fuel : Nat) (forest : (Nat → Nat × Nat))
    (i : Nat) : List (Nat × Nat) :=
  let tags := (Nat.rec (motive := fun _ => Nat → List (Nat × (Nat × Nat))) (fun _ => [])
    (fun _ previous j =>
      let (parent, token) := forest j
      if Nat.beq parent 0 then dagTagRoot root token
      else dagTagStep mask (fullMask width) token (previous (parent-1))) (fuel+1)) i
  List.rec [] (fun tag _ rest => tag.2 :: rest) tags

def dagPackWords (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ tail => (w &&& fullMask 512) ||| (tail <<< 512)) ws

def dagLaneMarks (n : Nat) : Nat :=
  Nat.rec 0 (fun _ more => 1 ||| (more <<< 512)) n

def dagOmitted (a b : Nat) (left right : Bool) : Nat :=
  (if left then 0 else 1 <<< (512*a)) ||| (if right then 0 else 1 <<< (512*b))

def dagPackedPair (mask goal packed marks erased out : Nat) (directed : Bool) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    dagForceWord code (fun code =>
      dagForceWord (code &&& 511) (fun p =>
        dagForceWord (code >>> 9) (fun n =>
          let up := (packed >>> p) &&& marks
          let down := (packed >>> n) &&& marks
          let contrast := if directed then up &&& (down ^^^ marks) else up ^^^ down
          let gateOK := if directed then !out.testBit p || out.testBit n else out.testBit p == out.testBit n
          goal.testBit p && mask.testBit n && !goal.testBit n && Nat.blt p 512 && Nat.blt n 512 &&
            gateOK && Nat.beq (contrast &&& (marks ^^^ erased)) 0)))

theorem dagPackBits {ws : List Nat} {i row : Nat} (inside : i < ws.length) (width : row < 512) :
    (dagPackWords ws).testBit (512*i+row) = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp at inside
  | cons w ws ih =>
    change ((w &&& fullMask 512) ||| (dagPackWords ws <<< 512)).testBit (512*i+row) = _
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp [fullMask, Nat.testBit_two_pow_sub_one, width, Nat.not_le.mpr width]
    | succ i =>
      have hi : i < ws.length := by simpa using inside
      have crossed : 512 ≤ 512*i.succ+row := by omega
      have offset : 512*i.succ+row-512 = 512*i+row := by omega
      have past : ¬ 512*i.succ+row < 512 := by omega
      simp [crossed, offset, fullMask, Nat.testBit_two_pow_sub_one, past, ih hi]

theorem dagMarkBits {length i : Nat} (inside : i < length) :
    (dagLaneMarks length).testBit (512*i) = true := by
  induction length generalizing i with
  | zero => omega
  | succ length ih =>
    change (1 ||| (dagLaneMarks length <<< 512)).testBit (512*i) = true
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have hi : i < length := by omega
      have crossed : 512 ≤ 512*i.succ := by omega
      have offset : 512*i.succ-512 = 512*i := by omega
      simp [crossed, offset, ih hi]

def dagCheckChildren (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (reference : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (sample : (Nat × Nat)) (tags : List (Nat × Nat)) : Bool :=
  let n := state.2.1.length
  (n ≤ 64) && !state.2.1.contains goal &&
  dagForceWord (dagPackWords state.2.1) (fun packed =>
    dagForceWord (dagLaneMarks n) (fun marks =>
      dagForceCache tags (fun tags =>
    dagForceWord (fullMask sample.2) (fun full =>
      dagCountSigns false full tags (fun normal =>
        dagCountSigns true full tags (fun tight =>
          let visit := fun a b op retains =>
            dagForceWord (state.2.1.getD a 0) (fun x =>
              dagForceWord (state.2.1.getD b 0) (fun y =>
                dagForceWord (dagGateWord mask op x y) (fun out =>
                  let xs := tags.getD a (0,0)
                  let ys := tags.getD b (0,0)
                  dagForceWord (dagGateWord full op xs.1 ys.1) (fun up =>
                    dagForceWord (dagGateWord full op xs.2 ys.2) (fun down =>
                      treeBlock 0 retains (fun keep =>
                        let token := gateToken a b op keep
                        if dagTooWide n state.1 token then true else
                          let directed := dagSizeFloor n op keep == (state.1-1)+1
                          let pairs := dagSampleMiss sample full normal tight xs ys (up,down) directed op keep
                          let erased := dagOmitted a b (keep.testBit 0) (op == 2 || keep.testBit 1)
                          if dagPackedPair mask goal packed marks erased out directed pairs then true
                          else match dagDirectChild mask state a b op keep x y out with
                          | none => true
                          | some (fuel, ws, history) => dagForceWords ws (fun forced =>
                            let child := (fuel, forced, history)
                            reference token child || dagLocal mask goal chart cut child)))))))
          treeBlock 0 n (fun a =>
            visit a a 2 2 && treeBlock (a+1) (n-(a+1)) (fun b =>
              treeBlock 0 2 (fun op => visit a b op 4)))))))))

def dagStateOK (mask : Nat) (ws : List Nat) : Bool :=
  (ws.dedup.length == ws.length) && ws.all (fun w => w &&& mask == w)

theorem dagStateOKSpec {mask : Nat} {ws : List Nat} (ok : dagStateOK mask ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked mask w := by
  simp only [dagStateOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  exact ⟨List.nodup_iff_length_dedup_eq.mpr ok.1, ok.2⟩

def dagCheckNode (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))) (links : (Nat → Nat → Option (Nat × Nat)))
    (sample : (Nat × Nat)) (tags : Nat → List (Nat × Nat)) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, history) => dagForceWords ws (fun forced =>
      dagStateOK mask forced && dagCheckChildren mask goal chart cut
        (dagRef count states moves links (i+1)) (fuel, forced, history) sample (tags i))

def dagCheckRoots (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (witnesses : List (Nat × Nat × Nat)) (reference : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool) (stock : List Nat)
    (fuel : Nat) : Bool :=
  treeBlock 0 (2^stock.length) fun token =>
    let state := rootState stock fuel token
    !dagAllowedRoot witnesses state.2.1 || dagLocal mask goal chart cut state || reference token state

theorem dagLocalOpen {mask goal : Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (masked : Masked mask goal) (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (viable : WordViable mask goal state) (noCut : cut state = false) :
    dagLocal mask goal chart cut state = false := by
  obtain ⟨fuel,ws,history⟩ := state
  have ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel at cap
  have card := (liveWordSize live).2
  rw [List.toFinset_card_of_nodup nd] at card
  change ws.length + t ≤ k + 1 at card
  have fit : ¬ ws.length > fuel + 1 := by omega
  by_cases hz : fuel = 0
  · have kz : k = 0 := by omega
    subst k
    obtain ⟨_,eq,_⟩ := live
    have hm : goal ∈ ws := List.mem_toFinset.mp (by rw [eq]; simp)
    simp [dagLocal, fit, hm]
  by_cases tight : ws.length = fuel + 1
  · have ht : t = 0 := by omega
    subst t
    have dir := dagPartitionLive (directed := true) masked live (fun _ => rfl)
    have noChart : chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c))) = false := by
      cases opt : chart with
      | none => rfl
      | some c =>
        have vt : WordViable mask goal (fuel,ws,[]) := viable
        have ok := tightChart (chartOK c opt) tight vt
        simp [ok]
    simp [dagLocal, fit, hz, tight, dir, noCut, noChart]
  · have sep := dagPartitionLive (directed := false) masked live (by simp)
    simp [dagLocal, fit, hz, tight, sep, noCut]

theorem dagInsertLength (w : Nat) (ws : List Nat) :
    (insertWord w ws).length = ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons a ws ih =>
    change (if w ≤ a then w :: a :: ws else a :: insertWord w ws).length = _
    split <;> simp [ih]

theorem dagKeepLength (keep : Bool) (w : Nat) (ws : List Nat) :
    ws.length - (if keep then 0 else 1) ≤ (keepWord keep w ws).length := by
  cases keep
  · exact List.le_length_erase
  · simp [keepWord]

theorem dagWideChild {mask token : Nat} {state child : (Nat × List Nat × List (Nat × Nat × Nat))}
    (eval : childState mask token state = some child)
    (wide : dagTooWide state.2.1.length state.1 token = true) :
    child.2.1.length > child.1 + 1 := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let i := token / (4 * 3 * 64)
  let j := token / (4 * 3) % 64
  let x := ws.getD i 0
  let y := ws.getD j 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let a := keep.testBit 0
  let b := op == 2 || keep.testBit 1
  let rest := keepWord b y (keepWord a x ws)
  let bad : Bool := fuel == 0 || j ≥ ws.length || (if op == 2 then i != j || keep ≥ 2 else i ≥ j)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  rw [← eq]
  change (insertWord z rest).length > fuel - 1 + 1
  rw [dagInsertLength]
  have h1 := dagKeepLength a x ws
  have h2 := dagKeepLength b y (keepWord a x ws)
  have h : ws.length - (if a then 0 else 1) - (if b then 0 else 1) + 1 > fuel - 1 + 1 :=
    of_decide_eq_true wide
  dsimp only [rest]
  omega

theorem dagKeepMem {ws : List Nat} {x w : Nat} {keep : Bool}
    (nd : ws.Nodup) (h : w ∈ keepWord keep x ws) : w ∈ ws ∧ (keep = true ∨ w ≠ x) := by
  cases keep
  · simpa [keepWord, nd.mem_erase_iff, and_comm] using h
  · simpa [keepWord] using h

theorem dagKeepNodup {ws : List Nat} (nd : ws.Nodup) (keep : Bool) (x : Nat) :
    (keepWord keep x ws).Nodup := by
  cases keep
  · exact nd.erase x
  · exact nd

theorem dagPackedPairSound {mask goal out : Nat} {ws : List Nat} {directed : Bool}
    {pairs : List Nat} {a b : Nat} {left right : Bool}
    (nd : ws.Nodup)
    (checked : dagPackedPair mask goal (dagPackWords ws) (dagLaneMarks ws.length)
      (dagOmitted a b left right) out directed pairs = true) :
    dagPairReject mask goal directed
      (out :: keepWord right (ws.getD b 0) (keepWord left (ws.getD a 0) ws)) pairs = true := by
  obtain ⟨code,mem,verdict⟩ := List.any_eq_true.mp checked
  apply List.any_eq_true.mpr
  refine ⟨code,mem,?_⟩
  simp only [dagForceWordEq, Bool.and_eq_true, Nat.blt_eq] at verdict
  obtain ⟨⟨⟨⟨⟨⟨hp, hn⟩, neg⟩, wp⟩, wn⟩, output⟩, closure⟩ := verdict
  refine Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨
    Bool.and_eq_true_iff.mpr ⟨hp,hn⟩,neg⟩,List.all_eq_true.mpr ?_⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | later
  · exact output
  have rightMem := dagKeepMem (dagKeepNodup nd left (ws.getD a 0)) later
  have leftMem := dagKeepMem nd rightMem.1
  obtain ⟨i,inside,eq⟩ := List.mem_iff_getElem.mp leftMem.1
  have atIndex : ws.getD i 0 = w := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inside] using eq
  have omitted : (dagOmitted a b left right).testBit (512*i) = false := by
    have cleared (j : Nat) (keep : Bool) (h : keep = true ∨ w ≠ ws.getD j 0) :
        (if keep then 0 else 1 <<< (512*j)).testBit (512*i) = false := by
      rcases h with yes | diff
      · simp [yes]
      · have ne : i ≠ j := fun same => diff (same ▸ atIndex).symm
        cases keep <;> simp [Nat.shiftLeft_eq, Nat.testBit_two_pow, show 512*j ≠ 512*i by omega]
    simp [dagOmitted, Nat.testBit_or, cleared a left leftMem.2, cleared b right rightMem.2]
  let p := code &&& 511
  let n := code >>> 9
  let marks := dagLaneMarks ws.length
  let signal := dagPackWords ws
  have mark : marks.testBit (512*i) = true := dagMarkBits inside
  have test {j : Nat} (within : j < 512) :
      ((signal >>> j) &&& marks).testBit (512*i) = w.testBit j := by
    rw [Nat.testBit_and, Nat.testBit_shiftRight, mark, Bool.and_true,
      Nat.add_comm j, dagPackBits inside within, atIndex]
  have h := congrArg (fun word => Nat.testBit word (512*i)) (Nat.beq_eq.mp closure)
  simp only [Nat.zero_testBit] at h
  change (((if directed then (signal >>> p &&& marks) &&& ((signal >>> n &&& marks) ^^^ marks)
      else (signal >>> p &&& marks) ^^^ (signal >>> n &&& marks)) &&&
    (marks ^^^ dagOmitted a b left right)).testBit (512*i)) = false at h
  have pt := test (j := p) wp
  have nt := test (j := n) wn
  cases directed <;> cases px : w.testBit p <;> cases nx : w.testBit n <;>
    simp [px,nx,pt,nt,Nat.testBit_and,Nat.testBit_xor,mark,omitted,p,n] at h ⊢

theorem dagEarlyOpen {mask goal a b op keep out : Nat} {state child : (Nat × List Nat × List (Nat × Nat × Nat))}
    (masked : Masked mask goal) (viable : WordViable mask goal child)
    (parent : state.2.1.Nodup) (eval : dagDirectChild mask state a b op keep
      (state.2.1.getD a 0) (state.2.1.getD b 0) out = some child) (pairs : List Nat) :
    dagPackedPair mask goal (dagPackWords state.2.1) (dagLaneMarks state.2.1.length)
      (dagOmitted a b (keep.testBit 0) (op == 2 || keep.testBit 1)) out
      (dagSizeFloor state.2.1.length op keep == (state.1-1)+1) pairs = false := by
  obtain ⟨fuel,ws,history⟩ := state
  let x := ws.getD a 0
  let y := ws.getD b 0
  apply Bool.eq_false_iff.mpr
  intro closed
  have closed := dagPackedPairSound parent closed
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := out == 0 || out == mask || ws.contains out
  let bank := dagKept ws op keep x y
  change (if bad then none else if stale then none else
    some (fuel-1, insertWord out bank, (out,x,y)::history)) = some child at eval
  by_cases h : bad = true
  · simp [h] at eval
  by_cases h' : stale = true
  · simp [h,h'] at eval
  have eq : (fuel-1,insertWord out bank,(out,x,y)::history) = child := by simpa [h,h'] using eval
  subst child
  obtain ⟨nd,k,t,cap,live⟩ := viable
  change k ≤ fuel-1 at cap
  have size := (liveWordSize live).2
  change (insertWord out bank : List Nat).toFinset.card + t ≤ k+1 at size
  rw [List.toFinset_card_of_nodup nd, dagInsertLength] at size
  have same : (out::bank).toFinset = (insertWord out bank).toFinset := by
    ext w
    simp only [List.mem_toFinset, List.mem_cons, insertWordMem]
  have openBank := dagPairsOpen (pairs := pairs)
    (directed := dagSizeFloor ws.length op keep == (fuel-1)+1) masked (show LiveWord mask goal k t (out::bank).toFinset by rwa [same])
  have available : (dagSizeFloor ws.length op keep == (fuel-1)+1) = true → t = 0 := by
    intro directed
    have exactBudget := beq_iff_eq.mp directed
    have first := dagKeepLength (keep.testBit 0) x ws
    have second := dagKeepLength (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
    change dagSizeFloor ws.length op keep = (fuel-1)+1 at exactBudget
    unfold dagSizeFloor at exactBudget
    dsimp only [bank, dagKept] at size
    omega
  have refuses := openBank available
  exact Bool.noConfusion (closed.symm.trans refuses)

theorem dagChildAt {mask goal : Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)} {ref : Nat → (Nat × List Nat × List (Nat × Nat × Nat)) → Bool} {state child : (Nat × List Nat × List (Nat × Nat × Nat))} {sample : (Nat × Nat)} {tags : List (Nat × Nat)} {a b op keep : Nat}
    (checked : dagCheckChildren mask goal chart cut ref state sample tags = true)
    (ha : a < state.2.1.length)
    (legal : (a = b ∧ op = 2 ∧ keep < 2) ∨ (a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4))
    (eval : childState mask (gateToken a b op keep) state = some child)
    (masked : Masked mask goal) (viable : WordViable mask goal child) (nd : state.2.1.Nodup)
    (openChild : dagLocal mask goal chart cut child = false) :
    ref (gateToken a b op keep) child = true := by
  have narrow : dagTooWide state.2.1.length state.1 (gateToken a b op keep) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have tooMany := dagWideChild eval h
    obtain ⟨f,w,path⟩ := child
    simp [dagLocal, tooMany] at openChild
  simp only [dagCheckChildren, dagForceCacheEq, dagForceWordEq, dagCountSignsEq,
    Bool.and_eq_true, decide_eq_true_eq] at checked
  have width := checked.1.1
  have atA := treeBlock_at checked.2 (i := a) (Nat.zero_le _) (by simpa using ha)
  rcases Bool.and_eq_true_iff.mp atA with ⟨unary,binary⟩
  rcases legal with ⟨rfl,rfl,hk⟩ | ⟨ab,hb,hop,hk⟩
  · have atKeep := treeBlock_at unary (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := dagDirectChildEq (mask := mask) (state := state) (a := a) (b := a) (op := 2)
      (keep := keep) (by omega) (by decide) (by omega)
    have direct := fields.trans eval
    have early := dagEarlyOpen masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,dagForceWordsEq,early,openChild,Bool.or_false] using atKeep
  · have atB := treeBlock_at binary (i := b) (by omega) (by omega)
    have atOp := treeBlock_at atB (i := op) (Nat.zero_le _) (by simpa using hop)
    have atKeep := treeBlock_at atOp (i := keep) (Nat.zero_le _) (by simpa using hk)
    have fields := dagDirectChildEq (mask := mask) (state := state) (a := a) (b := b) (op := op)
      (keep := keep) (by omega) (by omega) hk
    have direct := fields.trans eval
    have early := dagEarlyOpen masked viable nd direct
    rcases child with ⟨fuel,ws,history⟩
    simpa only [narrow,Bool.false_eq_true,ite_false,fields,eval,dagForceWordsEq,early,openChild,Bool.or_false] using atKeep

theorem readWordMasked {mask : Nat} {ws : List Nat}
    (all : ∀ w ∈ ws, Masked mask w) (i : Nat) : Masked mask (ws.getD i 0) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => simp [Masked]
  | some w => exact all w (List.mem_of_getElem? h)

theorem childStateData {mask token : Nat} {state child : (Nat × List Nat × List (Nat × Nat × Nat))}
    (eval : childState mask token state = some child)
    (masked : ∀ w ∈ state.2.1, Masked mask w) :
    child.1 < state.1 ∧ ∀ w ∈ child.2.1, Masked mask w := by
  obtain ⟨fuel,ws,history⟩ := state
  let keep := token % 4
  let op := token / 4 % 3
  let a := token / (4 * 3 * 64)
  let b := token / (4 * 3) % 64
  let x := ws.getD a 0
  let y := ws.getD b 0
  let z := if op == 0 then x &&& y else if op == 1 then x ||| y else mask ^^^ x
  let rest := keepWord (op == 2 || keep.testBit 1) y (keepWord (keep.testBit 0) x ws)
  let bad : Bool := fuel == 0 || b ≥ ws.length || (if op == 2 then a != b || keep ≥ 2 else a ≥ b)
  let stale : Bool := z == 0 || z == mask || ws.contains z
  change (if bad then none else if stale then none else
    some (fuel - 1, insertWord z rest, (z,x,y) :: history)) = some child at eval
  by_cases hb : bad = true
  · simp [hb] at eval
  by_cases hs : stale = true
  · simp [hb,hs] at eval
  have eq : (fuel-1, insertWord z rest, (z,x,y) :: history) = child := by simpa [hb,hs] using eval
  subst child
  have pos : 0 < fuel := by
    by_contra! h
    have he : fuel = 0 := by omega
    simp [bad, he] at hb
  refine ⟨by dsimp; omega,?_⟩
  have read (i : Nat) : AvailableWord mask ws (ws.getD i 0) := by
    simp only [List.getD_eq_getElem?_getD]
    cases h : ws[i]? with
    | none => exact Or.inl rfl
    | some a => exact Or.inr (Or.inr (List.mem_of_getElem? h))
  have hm : Masked mask z := by
    apply maskedGate masked
    unfold z
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inl rfl⟩
    split
    · exact Or.inr ⟨x,y,read _,read _,Or.inr rfl⟩
    · exact Or.inl ⟨x,read _,rfl⟩
  intro w hw
  rcases insertWordMem.mp hw with rfl | other
  · exact hm
  · apply masked w
    apply keepSubset (keep.testBit 0) x ws w
    exact keepSubset (op == 2 || keep.testBit 1) y _ w other

def DagMovesOK (mask goal : Nat) (width : Nat) (moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))) : Prop :=
  ∀ (i : Nat) (m : (List (List (Nat × Nat) × List (Nat × Nat)))), moves[i]? = some m →
    ∃ select : Fin width → Fin width, DagAuto mask goal select ∧
      ∀ w, Masked mask w → mixMove m w = relabel select w


def dagMoves (cert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width)))) : Array (List (List (Nat × Nat) × List (Nat × Nat))) := (cert.map Prod.fst).toArray

def dagMoveRecordProps {width : Nat} (mask goal : Nat) (entry : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width))) : Prop :=
  let (move, select, inverse) := entry
  (∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal

def dagMoveRecordOK {width : Nat} (mask goal : Nat) (entry : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width))) : Bool :=
  let (move, select, inverse) := entry
  decide ((∀ i, inverse (select i) = i) ∧ (∀ i, select (inverse i) = i) ∧
    (mask &&& fullMask width = mask) ∧ (goal &&& mask = goal) ∧
    (∀ i : Fin width, mask.testBit i.val = true →
      mixMove move (2 ^ i.val) = 2 ^ (inverse i).val) ∧
    mixMove move mask = mask ∧ mixMove move goal = goal)

theorem dagMoveRecordSpec {width : Nat} {mask goal : Nat} {entry : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width))}
    (ok : dagMoveRecordOK mask goal entry = true) : dagMoveRecordProps mask goal entry := by
  rcases entry with ⟨move,select,inverse⟩
  unfold dagMoveRecordProps
  exact of_decide_eq_true ok

theorem dagMovesOfCheck {width : Nat} {mask goal : Nat} {cert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin width → Fin width) × (Fin width → Fin width)))}
    (ok : cert.all (dagMoveRecordOK mask goal) = true) :
    DagMovesOK mask goal width (dagMoves cert) := by
  intro i m get
  simp only [dagMoves, List.getElem?_toArray, List.getElem?_map] at get
  cases e : cert[i]? with
  | none => simp [e] at get
  | some entry =>
    have eq : entry.1 = m := by simpa [e] using get
    rcases entry with ⟨move,select,inverse⟩
    obtain ⟨left,right,bm,gm,basis,mm,mg⟩ :=
      dagMoveRecordSpec (List.all_eq_true.mp ok _ (List.mem_of_getElem? e))
    subst m
    exact ⟨select, dagAutoFromMove left right bm gm basis mm mg⟩

theorem dagLinked {mask goal : Nat} {width count : Nat} {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))}
    {moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))} {links : (Nat → Nat → Option (Nat × Nat))} {parent token : Nat} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (bounds : Masked (fullMask width) mask)
    (valid : DagMovesOK mask goal width moves)
    (masked : ∀ w ∈ state.2.1, Masked mask w)
    (ok : dagRef count states moves links parent token state = true)
    {k t : Nat} (live : LiveWord mask goal k t state.2.1.toFinset) :
    ∃ i saved, i < count ∧ states i = some saved ∧ saved.1 = state.1 ∧
      LiveWord mask goal k t saved.2.1.toFinset := by
  unfold dagRef at ok
  split at ok
  · contradiction
  next destination auto h =>
    have hd := Nat.blt_eq.mp (Bool.and_eq_true_iff.mp ok).1
    have finish := (Bool.and_eq_true_iff.mp ok).2
    cases eq : states destination with
    | none => simp [eq] at finish
    | some saved =>
      simp only [eq, Bool.and_eq_true, beq_iff_eq] at finish
      refine ⟨destination,saved,hd,eq,finish.1,?_⟩
      have last := finish.2
      split at last
      · have same : saved.2.1 = state.2.1 := beq_iff_eq.mp last
        rwa [same]
      · split at last
        · contradiction
        next m hm =>
          obtain ⟨select,auto,agree⟩ := valid _ _ hm
          have same : saved.2.1 = dagMoveWords m state.2.1 := beq_iff_eq.mp last
          rw [same, dagMoveSet (fun w hw => agree w (masked w hw))]
          exact liveMaskedImage auto bounds live (fun w hw => masked _ (List.mem_toFinset.mp hw))

theorem dagAllNodes {mask goal : Nat} {width fuel count : Nat}
    {stock : List Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {cut : ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)} {forest : (Nat → Nat × Nat)} {moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))} {links : (Nat → Nat → Option (Nat × Nat))} {sample : (Nat × Nat)}
    {tags : Nat → List (Nat × Nat)}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (cutSound : ∀ s, WordViable mask goal s → cut s = false)
    (autos : DagMovesOK mask goal width moves)
    (verified : treeBlock 0 count (dagCheckNode mask goal chart cut count
      (dagTrace mask stock fuel forest) moves links sample tags) = true):
    ∀ cap i saved, i < count → dagTrace mask stock fuel forest i = some saved →
      saved.1 = cap → ∀ k t, k ≤ cap → ¬LiveWord mask goal k t saved.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i s iBound stateEq sFuel k t kBound live
    rcases s with ⟨remaining, words, history⟩
    let s : (Nat × List Nat × List (Nat × Nat × Nat)) := (remaining, words, history)
    let states := dagTrace mask stock fuel forest
    change states i = some s at stateEq
    have checked := treeBlock_at verified (Nat.zero_le i) (by simpa using iBound)
    change dagCheckNode mask goal chart cut count states moves links sample tags i = true at checked
    simp only [dagCheckNode, stateEq, dagForceWordsEq, Bool.and_eq_true] at checked
    obtain ⟨nd,masked⟩ := dagStateOKSpec checked.1
    have ok := checked.2
    have viable : WordViable mask goal s := ⟨nd,k,t,sFuel ▸ kBound,live⟩
    have scanned := ok
    simp only [dagCheckChildren, Bool.and_eq_true, decide_eq_true_eq] at scanned
    have wide := scanned.1.1
    have absent := scanned.1.2
    rcases wordProgress wide viable with hit | ⟨child, possible, cv⟩
    · simpa [hit] using absent
    obtain ⟨a,b,op,keep,ha,legal,eval⟩ := possible
    have r := dagChildAt ok ha legal eval goalMask cv nd (dagLocalOpen goalMask chartOK cv (cutSound _ cv))
    have ⟨less,cm⟩ := childStateData eval masked
    have below : child.1 < cap := sFuel ▸ less
    obtain ⟨_,k',t',fits,clive⟩ := cv
    obtain ⟨j,dest,bound,restore,fuelEq,tail⟩ :=
      dagLinked maskBounds autos cm r clive
    exact ih child.1 below j dest bound restore fuelEq k' t' fits tail

theorem lowerDag {mask goal : Nat} {width fuel count : Nat}
    {stock : List Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {forest : (Nat → Nat × Nat)} {moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))} {links : (Nat → Nat → Option (Nat × Nat))} {sample : (Nat × Nat)}
    {tags : Nat → List (Nat × Nat)}
    {bounds : List (Nat × List Nat × Nat × Nat)} {witnesses : List (Nat × Nat × Nat)}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal) (proper : properWord mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (autos : DagMovesOK mask goal width moves)
    (stockMasked : ∀ w ∈ stock, Masked mask w) (stockNd : stock.Nodup)
    (essential : witnesses.all (essentialB mask goal stock) = true)
    (known : Known bounds) (submasks : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (rootCheck : dagCheckRoots mask goal chart (dagKnownCloses goal bounds) witnesses
      (dagRef count (dagTrace mask stock fuel forest) moves links 0)
      stock fuel = true)
    (nodeCheck : treeBlock 0 count (dagCheckNode mask goal chart (dagKnownCloses goal bounds)
      count (dagTrace mask stock fuel forest) moves links sample tags) = true) :
    Lower mask stock goal (fuel+1) := by
  intro values build hit
  by_contra! small
  obtain ⟨k,t,S,hk,live,sub⟩ := extractWordLive stockMasked build hit proper
  have included : S ⊆ stock.toFinset := fun w hw => List.mem_toFinset.mpr (sub w hw)
  obtain ⟨token,tokenBound,eq⟩ := rootToken stock S
  rw [Finset.inter_eq_right.mpr included] at eq
  let state := rootState stock fuel token
  have eq' : state.2.1.toFinset = S := eq
  have v : WordViable mask goal state := by
    refine ⟨(rootWordSublist stock token).nodup stockNd,k,t,?_,?_⟩
    · change k ≤ fuel
      omega
    · rwa [eq']
  have cutOpen (s : (Nat × List Nat × List (Nat × Nat × Nat))) (h : WordViable mask goal s) : dagKnownCloses goal bounds s = false := by
    rw [dagKnownClosesEq]
    exact knownClosesSound known submasks h
  have openRoot := dagLocalOpen goalMask chartOK v (cutOpen _ v)
  have allowed : dagAllowedRoot witnesses state.2.1 = true := by
    apply List.all_eq_true.mpr
    intro entry mem
    apply List.contains_iff_mem.mpr
    rw [← List.mem_toFinset, eq']
    exact essentialRequired (List.all_eq_true.mp essential entry mem) sub live
  have checked := treeBlock_at rootCheck (Nat.zero_le token) (by simpa using tokenBound)
  change (!dagAllowedRoot witnesses state.2.1 || dagLocal mask goal chart (dagKnownCloses goal bounds) state ||
    dagRef count (dagTrace mask stock fuel forest) moves links 0 token state) = true at checked
  simp only [allowed,openRoot,Bool.not_true,Bool.false_or] at checked
  have finish := dagAllNodes maskBounds goalMask chartOK cutOpen autos nodeCheck
  have fits : k ≤ fuel := by omega
  have still : LiveWord mask goal k t state.2.1.toFinset := by rwa [eq']
  have stateMask : ∀ w ∈ state.2.1, Masked mask w := by
    intro w hw
    exact stockMasked _ ((rootWordSublist stock token).subset hw)
  obtain ⟨i,s,hi,restore,cap,plan⟩ := dagLinked maskBounds autos stateMask checked still
  exact finish fuel i s hi restore cap k t fits plan

def dagLookupLinks (index data indexWidth sizeBits tokenBits destinationBits autoBits trials : Nat) :
    (Nat → Nat → Option (Nat × Nat)) := fun parent token =>
  let entry := unpack index indexWidth parent
  let size := entry &&& ((1 <<< sizeBits) - 1)
  let offset := entry >>> sizeBits
  let width := tokenBits + destinationBits + autoBits
  (Nat.rec (motive := fun _ => Nat → Nat → Option (Nat × Nat)) (fun _ _ => none)
    (fun _ next lo hi =>
      if Nat.blt lo hi then
        let mid := (lo+hi)/2
        let code := unpack data width mid
        let key := code &&& ((1 <<< tokenBits) - 1)
        if Nat.beq token key then
          some ((code >>> tokenBits) &&& ((1 <<< destinationBits) - 1),
            code >>> (tokenBits + destinationBits))
        else if Nat.blt token key then next lo mid else next (mid+1) hi
      else none) trials) offset (offset+size)

def projectDAGStock (mask : Nat) (source : List Nat) (indices : List Nat) : List Nat :=
  List.rec [] (fun i _ rest => (mask &&& source.getD i 0) :: rest) indices

theorem stockMaskedOfCheck {mask : Nat} {stock : List Nat}
    (h : stock.all (fun w => w &&& mask == w) = true) :
    ∀ w ∈ stock, Masked mask w := by
  intro w hw
  exact beq_iff_eq.mp (List.all_eq_true.mp h w hw)

theorem suppliesOfCheck {oldMask : Nat} {old new : List Nat} {rename : Nat → Nat}
    (h : new.all (fun w => availableB oldMask old (rename w)) = true) :
    ∀ w ∈ new, AvailableWord oldMask old (rename w) := by
  intro w hw
  exact availableB_spec.mp (List.all_eq_true.mp h w hw)

def dagShift (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (word : Nat) : Nat :=
  mixMove move (word &&& mask)

def dagShiftUnique (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : Nat → Nat → Bool :=
  Nat.rec (fun _ => true) (fun i next occupied =>
    if mask.testBit i then
      dagForceWord (mixMove move (2^i)) (fun col =>
        Nat.beq (col &&& occupied) 0 && dagForceWord (occupied ||| col) next)
    else next occupied)

theorem dagShiftLinear (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : BitLinear (dagShift mask move) := by
  apply bitLinearComp (mixMoveLinear move)
  simpa using bitLinearRight mask 0

theorem dagShiftBasis (mask : Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (i : Nat) :
    dagShift mask move (2 ^ i) = if mask.testBit i then mixMove move (2^i) else 0 := by
  have select : 2 ^ i &&& mask = if mask.testBit i then 2^i else 0 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases same : i = j
    · subst j
      simp only [Nat.testBit_and, Nat.testBit_two_pow, decide_true, Bool.true_and]
      cases mask.testBit i <;> simp
    · cases h : mask.testBit i <;> simp [Nat.testBit_and, Nat.testBit_two_pow, same, h]
  rw [dagShift, select]
  split
  · rfl
  · apply Nat.eq_of_testBit_eq
    intro j
    apply Bool.eq_iff_iff.mpr
    rw [mixMoveLinear]
    simp

theorem dagShiftUniqueSpec {mask : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))} {n : Nat} {occupied : Nat}
    (ok : dagShiftUnique mask move n occupied = true) :
    (∀ j < n, ∀ b, (dagShift mask move (2^j)).testBit b = true → occupied.testBit b = false) ∧
    (∀ j < n, ∀ k < n, ∀ b, (dagShift mask move (2^j)).testBit b = true →
      (dagShift mask move (2^k)).testBit b = true → j = k) := by
  induction n generalizing occupied with
  | zero => simp
  | succ n ih =>
    let col := mixMove move (2^n)
    change (if mask.testBit n then dagForceWord col (fun w =>
      Nat.beq (w &&& occupied) 0 && dagForceWord (occupied ||| w) (dagShiftUnique mask move n))
      else dagShiftUnique mask move n occupied) = true at ok
    cases active : mask.testBit n
    · simp [active,dagForceWordEq] at ok
      obtain ⟨existing,unique⟩ := ih ok
      have dead : dagShift mask move (2^n) = 0 := by simp [dagShiftBasis,active]
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · simp [same,dead] at h
        · exact existing j (by omega) b h
      · intro j hj k hk b a c
        by_cases e : j = n
        · simp [e,dead] at a
        by_cases e' : k = n
        · simp [e',dead] at c
        exact unique j (by omega) k (by omega) b a c
    · simp only [active,ite_true,dagForceWordEq,Bool.and_eq_true] at ok
      have disjoint := Nat.beq_eq.mp ok.1
      obtain ⟨existing,unique⟩ := ih ok.2
      have colEq : dagShift mask move (2^n) = col := by simp [dagShiftBasis,active,col]
      have old {j b : Nat} (hj : j < n) (h : (dagShift mask move (2^j)).testBit b = true) :
          occupied.testBit b = false ∧ col.testBit b = false := by
        simpa [Nat.testBit_or, Bool.or_eq_false_iff] using existing j hj b h
      refine ⟨?_,?_⟩
      · intro j hj b h
        by_cases same : j = n
        · rw [same,colEq] at h
          have bit := congrArg (fun w => Nat.testBit w b) disjoint
          simpa [Nat.testBit_and,h] using bit
        · exact (old (by omega) h).1
      · intro j hj k hk b a c
        by_cases e : j = n
        · by_cases e' : k = n
          · exact e.trans e'.symm
          · rw [e,colEq,(old (by omega) c).2] at a
            contradiction
        by_cases e' : k = n
        · rw [e',colEq,(old (by omega) a).2] at c
          contradiction
        exact unique j (by omega) k (by omega) b a c

theorem dagShiftGates {mask : Nat} {move : (List (List (Nat × Nat) × List (Nat × Nat)))} {width : Nat}
    (bounded : Masked (fullMask width) mask) (checked : dagShiftUnique mask move width 0 = true) :
    (∀ a b, dagShift mask move (a &&& b) = dagShift mask move a &&& dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ||| b) = dagShift mask move a ||| dagShift mask move b) ∧
    (∀ a b, dagShift mask move (a ^^^ b) = dagShift mask move a ^^^ dagShift mask move b) := by
  let f := dagShift mask move
  have lin := dagShiftLinear mask move
  have uniq {j k i : Nat} (hj : (f (2^j)).testBit i = true) (hk : (f (2^k)).testBit i = true) : j = k := by
    have within {m : Nat} (a : (f (2^m)).testBit i = true) : m < width := by
      by_contra! big
      have eq := congrArg (fun w => Nat.testBit w m) bounded
      have zero : mask.testBit m = false := by
        simpa [Masked,fullMask,Nat.testBit_and,Nat.testBit_two_pow_sub_one,show ¬m < width by omega] using eq.symm
      simp [f,dagShiftBasis,zero] at a
    exact (dagShiftUniqueSpec checked).2 j (within hj) k (within hk) i hj hk
  refine ⟨?_,?_,?_⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [Nat.testBit_and, Bool.and_eq_true, lin, lin, lin]
    constructor
    · rintro ⟨j,hj,h⟩
      rw [Nat.testBit_and, Bool.and_eq_true] at hj
      exact ⟨⟨j,hj.1,h⟩,⟨j,hj.2,h⟩⟩
    · rintro ⟨⟨j,hj,q⟩,⟨k,hk,r⟩⟩
      have same := uniq q r
      subst k
      exact ⟨j,by simp [Nat.testBit_and,hj,hk],q⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    apply Bool.eq_iff_iff.mpr
    rw [lin (a ||| b) i, Nat.testBit_or, Bool.or_eq_true, lin a i, lin b i]
    simp only [Nat.testBit_or, Bool.or_eq_true]
    constructor
    · rintro ⟨j,(left | right),same⟩
      · exact Or.inl ⟨j,left,same⟩
      · exact Or.inr ⟨j,right,same⟩
    · rintro (⟨j,left,same⟩ | ⟨j,right,same⟩)
      · exact ⟨j,Or.inl left,same⟩
      · exact ⟨j,Or.inr right,same⟩
  · intro a b
    apply Nat.eq_of_testBit_eq; intro i
    have l := lin a i
    have r := lin b i
    have v := lin (a ^^^ b) i
    cases pa : (f a).testBit i <;> cases pb : (f b).testBit i
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      have disj : a.testBit j = true ∨ b.testBit j = true := by
        rw [Nat.testBit_xor] at hj
        cases aj : a.testBit j <;> cases bj : b.testBit j <;> simp [aj,bj] at hj ⊢
      rcases disj with da | db
      · have := l.mpr ⟨j,da,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this
      · have := r.mpr ⟨j,db,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := r.mp pb
      have notA : a.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := l.mpr ⟨j,yes,h⟩
        change (f a).testBit i = true at this
        simp [pa] at this)
      exact ⟨j,by simp [Nat.testBit_xor,notA,hj],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply v.mpr
      obtain ⟨j,hj,h⟩ := l.mp pa
      have notB : b.testBit j = false := Bool.eq_false_iff.mpr (fun yes => by
        have := r.mpr ⟨j,yes,h⟩
        change (f b).testBit i = true at this
        simp [pb] at this)
      exact ⟨j,by simp [Nat.testBit_xor,hj,notB],h⟩
    · rw [Nat.testBit_xor,pa,pb]
      apply Bool.eq_false_iff.mpr
      intro yes
      obtain ⟨j,hj,h⟩ := v.mp yes
      obtain ⟨a',ha,q⟩ := l.mp pa
      obtain ⟨b',hb,r⟩ := r.mp pb
      have ea := uniq h q
      have eb := uniq h r
      rw [← ea] at ha
      rw [← eb] at hb
      simp [Nat.testBit_xor,ha,hb] at hj

def dagShiftCheck (width mask goal oldMask oldGoal : Nat) (stock old : List Nat) (move : (List (List (Nat × Nat) × List (Nat × Nat)))) : Bool :=
  Nat.beq (mask &&& fullMask width) mask && dagShiftUnique mask move width 0 &&
    Nat.beq (dagShift mask move mask) oldMask && Nat.beq (dagShift mask move goal) oldGoal &&
    stock.all (fun w => availableB oldMask old (dagShift mask move w))

theorem dagShiftLower {width mask goal oldMask oldGoal : Nat} {stock old : List Nat} {min : Nat}
    (move : (List (List (Nat × Nat) × List (Nat × Nat)))) (origin : Lower oldMask old oldGoal min)
    (ok : dagShiftCheck width mask goal oldMask oldGoal stock old move = true) :
    Lower mask stock goal min := by
  simp only [dagShiftCheck,Bool.and_eq_true,Nat.beq_eq] at ok
  obtain ⟨⟨⟨⟨bounded,unique⟩,masks⟩,goals⟩,supply⟩ := ok
  obtain ⟨andG,orG,xorG⟩ := dagShiftGates bounded unique
  have zero : dagShift mask move 0 = 0 := by
    apply Nat.eq_of_testBit_eq
    intro i
    apply Bool.eq_iff_iff.mpr
    rw [dagShiftLinear]
    simp
  apply lowerMap (dagShift mask move) zero masks (fun w => by rw [xorG,masks]) andG orG (suppliesOfCheck supply)
  rwa [goals]

def moveSchedule (stages : Array (List (Nat × Nat) × List (Nat × Nat))) (indices : List Nat) : (List (List (Nat × Nat) × List (Nat × Nat))) :=
  List.rec [] (fun i _ rest => stages[i]?.getD ([],[]) :: rest) indices

def hcsGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | PEqualNP.CircuitLowerBounds.GateOp.not => ~~~(args.headD 0)
  | _ => 0

def hcsStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [hcsGateVal bank g]

theorem hcsGetDBit {rows : Nat} (bank : List (BitVec rows)) (i : Nat) (k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem hcsAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem hcsOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem hcsGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (hcsGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl | rfl
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsAndBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, hcsOrBit, List.map_map]
    congr 1
    apply List.map_congr_left
    intro k _
    exact hcsGetDBit bank i.val k
  · simp only [hcsGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, BitVec.getLsbD_not, i.isLt,
      decide_true, Bool.true_and]
    cases ins with
    | nil => simp
    | cons k _ => simp only [List.map_cons, List.headD_cons, hcsGetDBit]

theorem hcsFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl hcsStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (hcsStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [hcsStep, List.map_append, List.map_cons, List.map_nil,
        hcsGateBit bank i g (hfan g List.mem_cons_self).1]
    rw [ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg')), hstep]

theorem hcsGateWord {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp))
    (hlen : g.inputs.length ≤ 2) :
    GateWord (fullMask rows) (bank.map BitVec.toNat) (hcsGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) :=
    Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl | rfl
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [hcsGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact gateOfAvailable (by simpa [hcsGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact gateOfAvailable (by simpa [hcsGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact Or.inr ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [hcsGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact Or.inl ⟨0, zeroAv, by simpa [hcsGateVal] using notNat (0 : BitVec rows)⟩
    | cons a _ => exact Or.inl ⟨_, toNatAvailable bank a, by simpa [hcsGateVal] using notNat (bank.getD a 0)⟩

theorem hcsBuilds {rows : Nat} (bank : List (BitVec rows))
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hfan : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or,
      PEqualNP.CircuitLowerBounds.GateOp.not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length = gs.length ∧ WordBuilds (fullMask rows) (bank.map BitVec.toNat) vs ∧
      ∀ v ∈ gs.foldl hcsStep bank, v.toNat ∈ vs ++ bank.map BitVec.toNat := by
  induction gs generalizing bank with
  | nil => exact ⟨[], rfl, trivial, fun _ h => List.mem_map_of_mem h⟩
  | cons g gs ih =>
    let v := hcsGateVal bank g
    have hg := hfan g List.mem_cons_self
    obtain ⟨xs, len, build, sub⟩ := ih (hcsStep bank g) (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
    have eq : (hcsStep bank g).map BitVec.toNat = bank.map BitVec.toNat ++ [v.toNat] := by
      simp [hcsStep, v]
    rw [eq] at build
    refine ⟨v.toNat :: xs, by simp [len], ⟨hcsGateWord bank g hg.1 hg.2, buildsWeaken ?_ build⟩, ?_⟩
    · intro u hu; exact Or.inr (Or.inr (by simpa [or_comm] using hu))
    · intro u hu; have m := sub u hu; rw [eq] at m
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using m

def hcsCheckPow (p : Nat → Bool) : Nat → Nat → Bool
  | 0, s => p s
  | k + 1, s => hcsCheckPow p k s && hcsCheckPow p k (s + 2 ^ k)

theorem hcsCheckPow_spec {p : Nat → Bool} {k s i : Nat}
    (h : hcsCheckPow p k s = true) (lo : s ≤ i) (hi : i < s + 2 ^ k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have e : i = s := by omega
    simpa [hcsCheckPow, e] using h
  | succ k ih =>
    simp only [hcsCheckPow, Bool.and_eq_true] at h
    by_cases hlt : i < s + 2 ^ k
    · exact ih h.1 lo hlt
    · exact ih h.2 (by omega) (by rw [Nat.pow_succ] at hi; omega)

theorem hcsLowerEq {m1 m2 g1 g2 min : Nat} {b1 b2 : List Nat}
    (hm : m1 = m2) (hb : b1 = b2) (hg : g1 = g2)
    (h : Lower m1 b1 g1 min) : Lower m2 b2 g2 min := by
  subst hm; subst hb; subst hg; exact h

theorem hcsEvalWord {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n)) 
    (f : (Fin n → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hev : ∀ x, C.eval (List.ofFn x) = f x) :
    (C.gates.foldl hcsStep raw).getD C.output 0 = goal := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let y : Fin n → Bool := fun k => j.testBit k.val
  have hbank : raw.map (fun v => v.getLsbD j) = List.ofFn y :=
    beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
  have hfg : goal.getLsbD j = f y :=
    beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le j) (Nat.zero_add _ ▸ hj))
  have hbits := hcsFoldBits raw ⟨j, hj⟩ C.gates hfan
  have hevj : (C.wires (List.ofFn y)).getD C.output false = f y := hev y
  change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (List.ofFn y)).getD C.output false = f y at hevj
  rw [← hbank, ← hbits] at hevj
  rw [hfg, ← hevj, ← hcsGetDBit]

theorem hcsLower {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n)) (min : Nat)
    (f : (Fin n → Bool) → Bool)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (claim : Lower (fullMask (2 ^ n)) (raw.map BitVec.toNat) goal.toNat min)
    (t : Nat) (h : PEqualNP.MetaComplexity.HasCircuitSize n f t) : min ≤ t := by
  obtain ⟨C, hfan, hsz, hev⟩ := h
  obtain ⟨vs, len, built, sub⟩ := hcsBuilds raw C.gates hfan
  let eb := C.gates.foldl hcsStep raw
  have same : eb.getD C.output 0 = goal := hcsEvalWord raw goal f hRaw hGoal C hfan hev
  have av : AvailableWord (fullMask (2 ^ n)) (vs ++ raw.map BitVec.toNat) goal.toNat := by
    rw [← same, List.getD_eq_getElem?_getD]
    cases h : eb[C.output]? with
    | none => exact Or.inl rfl
    | some v => exact Or.inr (Or.inr (sub v (List.mem_of_getElem? h)))
  have lb := claim vs built av
  have hs : C.gates.length ≤ t := hsz
  omega

def hcsBitsNat : {k : Nat} → (Fin k → Bool) → Nat
  | 0, _ => 0
  | k + 1, x => (if x 0 then 1 else 0) + 2 * hcsBitsNat (fun i : Fin k => x i.succ)

theorem hcsBitsNat_lt : ∀ {k : Nat} (x : Fin k → Bool), hcsBitsNat x < 2 ^ k
  | 0, _ => by simp [hcsBitsNat]
  | k + 1, x => by
    have ih := hcsBitsNat_lt (fun i : Fin k => x i.succ)
    simp only [hcsBitsNat, Nat.pow_succ]
    cases x 0
    · simp; omega
    · simp; omega

theorem hcsBitsNat_testBit : ∀ {k : Nat} (x : Fin k → Bool) (i : Fin k),
    (hcsBitsNat x).testBit i.val = x i
  | 0, _, i => Fin.elim0 i
  | k + 1, x, i => by
    refine Fin.cases ?_ ?_ i
    · simp only [hcsBitsNat, Fin.val_zero]
      cases x 0
      · simp [Nat.testBit_zero]
      · have hmod : (1 + 2 * hcsBitsNat (fun m : Fin k => x m.succ)) % 2 = 1 := by omega
        simp [Nat.testBit_zero, hmod]
    · intro j
      have ih := hcsBitsNat_testBit (fun m : Fin k => x m.succ) j
      have hdiv : ((if x 0 then 1 else 0) + 2 * hcsBitsNat (fun m : Fin k => x m.succ)) / 2 =
          hcsBitsNat (fun m : Fin k => x m.succ) := by
        cases x 0
        · simp
        · simp; omega
      simpa only [hcsBitsNat, Fin.val_succ, Nat.testBit_succ, hdiv] using ih

theorem hcsWitnessEval {n : Nat} (raw : List (BitVec (2 ^ n))) (goal : BitVec (2 ^ n))
    (C : PEqualNP.CircuitLowerBounds.Circuit) (f : (Fin n → Bool) → Bool)
    (hfan : PEqualNP.MetaComplexity.FanInTwo C)
    (hRaw : hcsCheckPow (fun r => (raw.map fun v => v.getLsbD r) == List.ofFn fun j : Fin n => r.testBit j.val) n 0 = true)
    (hGoal : hcsCheckPow (fun r => goal.getLsbD r == f (fun j : Fin n => r.testBit j.val)) n 0 = true)
    (hEval : (C.gates.foldl hcsStep raw).getD C.output 0 = goal) :
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  intro x
  let r := hcsBitsNat x
  have hr : r < 2 ^ n := hcsBitsNat_lt x
  have hx : x = fun j : Fin n => r.testBit j.val := by
    funext j
    exact (hcsBitsNat_testBit x j).symm
  rw [hx]
  have hbank : raw.map (fun v => v.getLsbD r) = List.ofFn fun j : Fin n => r.testBit j.val :=
    beq_iff_eq.mp (hcsCheckPow_spec hRaw (Nat.zero_le r) (Nat.zero_add _ ▸ hr))
  have hfg : goal.getLsbD r = f (fun j : Fin n => r.testBit j.val) :=
    beq_iff_eq.mp (hcsCheckPow_spec hGoal (Nat.zero_le r) (Nat.zero_add _ ▸ hr))
  have hbits := hcsFoldBits raw ⟨r, hr⟩ C.gates hfan
  change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
    (List.ofFn fun j : Fin n => r.testBit j.val)).getD C.output false =
      f (fun j : Fin n => r.testBit j.val)
  rw [← hbank, ← hbits, ← hcsGetDBit, hEval, hfg]


def qStage0 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff, 0), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 24)])
def qStage1 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55, 0), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0x5500550055005500550055005500550055005500550055005500550055005500, 7)])
def qStage2 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xaaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555, 0), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0x5555555500000000555555550000000055555555000000005555555500000000, 31)])
def qStage3 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff, 0), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff000000000000000000000000ffffffff0000000000000000, 32)])
def qStage4 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0x9999999999999999999999999999999999999999999999999999999999999999, 0), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x4444444444444444444444444444444444444444444444444444444444444444, 1)])
def qStage5 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])
def qStage6 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffff, 0), (0xffffffff00000000ffffffff00000000, 96)], [(0xffffffff00000000ffffffff00000000000000000000000000000000, 96)])
def qStage7 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])
def qStage8 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff, 0), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffff000000000000ffff000000000000ffff000000000000ffff00000000, 16)])
def qStage9 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33, 0), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x3300330033003300330033003300330033003300330033003300330033003300, 6)])
def qStage10 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f, 0), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4)])
def qStage11 : (List (Nat × Nat) × List (Nat × Nat)) := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 4)])
def qStage12 : (List (Nat × Nat) × List (Nat × Nat)) := ([], [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff, 16)])
def qStage13 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff00ff00ff00ff00ff00ff00ff00ff0000ff00ff00ff00ff00ff00ff00ff00ff, 0), (0xff00ff00ff00ff00ff00ff00ff00ff00, 120)], [(0xff00ff00ff00ff00ff00ff00ff00ff00000000000000000000000000000000, 120)])
def qStage14 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa55555555555555555555555555555555, 0), (0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 127)], [(0x5555555555555555555555555555555500000000000000000000000000000000, 127)])
def qStage15 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333, 0), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x3333000033330000333300003333000033330000333300003333000033330000, 14)])
def qStage16 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xaaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555, 0), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0x5555000055550000555500005555000055550000555500005555000055550000, 15)])
def qStage17 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f, 0), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 12)])
def qStage18 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xa5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a, 3)], [(0x5050505050505050505050505050505050505050505050505050505050505050, 3)])
def qStage19 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffff0000ffff00000000ffff0000ffffffff0000ffff00000000ffff0000ffff, 0), (0xffff0000ffff00000000000000000000ffff0000ffff0000, 48)], [(0xffff0000ffff00000000000000000000ffff0000ffff0000000000000000, 48)])
def qStage20 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffff0000ffff0000ffff0000ffff00000000ffff0000ffff0000ffff0000ffff, 0), (0xffff0000ffff0000ffff0000ffff0000, 112)], [(0xffff0000ffff0000ffff0000ffff00000000000000000000000000000000, 112)])
def qStage21 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf0f0f0f0f0f0f0f00f0f0f0f0f0f0f0ff0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f, 0), (0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0, 60)], [(0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f0000000000000000, 60)])
def qStage22 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f, 0), (0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 124)], [(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f00000000000000000000000000000000, 124)])
def qStage23 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xaaaaaaaaaaaaaaaa5555555555555555aaaaaaaaaaaaaaaa5555555555555555, 0), (0xaaaaaaaaaaaaaaaa0000000000000000aaaaaaaaaaaaaaaa, 63)], [(0x5555555555555555000000000000000055555555555555550000000000000000, 63)])
def qStage24 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])
def qStage25 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)])
def qStage26 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcccccccccccccccc3333333333333333cccccccccccccccc3333333333333333, 0), (0xcccccccccccccccc0000000000000000cccccccccccccccc, 62)], [(0x3333333333333333000000000000000033333333333333330000000000000000, 62)])
def qStage27 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff00ff00ff00ff0000ff00ff00ff00ffff00ff00ff00ff0000ff00ff00ff00ff, 0), (0xff00ff00ff00ff000000000000000000ff00ff00ff00ff00, 56)], [(0xff00ff00ff00ff000000000000000000ff00ff00ff00ff0000000000000000, 56)])
def qStages : Array (List (Nat × Nat) × List (Nat × Nat)) := #[qStage0, qStage1, qStage2, qStage3, qStage4, qStage5, qStage6, qStage7, qStage8, qStage9, qStage10, qStage11, qStage12, qStage13, qStage14, qStage15, qStage16, qStage17, qStage18, qStage19, qStage20, qStage21, qStage22, qStage23, qStage24, qStage25, qStage26, qStage27]
def qBase : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def qGoal : Nat := 0xfffffffffffffffefffffffffffefffeffffffeeffffffeefffeffeefefcaa00
def q0Mask : Nat := 0x30300000303
abbrev q0Goal : Nat := qGoal &&& q0Mask
abbrev q0StockWords : List Nat := projectDAGStock q0Mask qBase [0, 3, 5]
def q0Fact : (Nat × List Nat × Nat × Nat) := (q0Mask, q0StockWords, 4, q0Goal)
def q0Cuts : List (Nat × List Nat × Nat × Nat) := []
def q0Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 33, 40, 9, 9, 9, 9, 9, 9, 9, 9, 9, 1, 8, 32, 1, 1, 1, 1, 1, 1, 1, 1, 1], rfl⟩
def q0Sample : (Nat × Nat) := (0x8841028008244028100841009, 6)
def q0Witnesses := unpackWitnesses q0StockWords [16928, 282656, 544776]
def q0Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x9 0x7 2 1 3 1 3 2
def q0Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def q0Tags := dagTraceTags q0Mask 6 (dagTagBases q0StockWords 0x3676b 0x6468 6) 3 q0Data
def q0States := dagTrace q0Mask q0StockWords 3 q0Data
def q0Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q0Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q0Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q0Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q0Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q0Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q0Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q0Move3Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q0Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q0Move4Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q0MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [0]), q0Move0Map, q0Move0Inverse), ((moveSchedule qStages [1]), q0Move1Map, q0Move1Inverse), ((moveSchedule qStages [2, 0]), q0Move2Map, q0Move2Inverse), ((moveSchedule qStages [1, 0]), q0Move3Map, q0Move3Inverse), ((moveSchedule qStages [2]), q0Move4Map, q0Move4Inverse)]
def q0Moves := dagMoves q0MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0Autos : DagMovesOK q0Mask q0Goal 256 q0Moves := dagMovesOfCheck (by decide +kernel)
def q0Check := dagCheckNode q0Mask q0Goal q0Chart (dagKnownCloses q0Goal q0Cuts) 1 q0States q0Moves q0Links q0Sample q0Tags
def q0RootAt (token : Nat) : Bool :=
  let s := rootState q0StockWords 3 token
  !dagAllowedRoot q0Witnesses s.2.1 || dagLocal q0Mask q0Goal q0Chart (dagKnownCloses q0Goal q0Cuts) s ||
  dagRef 1 q0States q0Moves q0Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0RootBlock0 : treeBlock 0 8 q0RootAt = true := by decide +kernel
theorem q0Roots : dagCheckRoots q0Mask q0Goal q0Chart (dagKnownCloses q0Goal q0Cuts) q0Witnesses (dagRef 1 q0States q0Moves q0Links 0) q0StockWords 3 = true := q0RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0Block0 : treeBlock 0 1 q0Check = true := by decide +kernel
theorem q0Blocks : treeBlock 0 1 q0Check = true := q0Block0
theorem q0Known : Known q0Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q0Stock : Lower q0Mask q0StockWords q0Goal 4 := by
  apply lowerDag _ _ _ _ q0Autos _ _ _ q0Known _ q0Roots q0Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q0StockWords; decide +kernel
  · decide +kernel
  · simp only [q0Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def q1Mask : Nat := 0x3030000000000000303
abbrev q1Goal : Nat := qGoal &&& q1Mask
abbrev q1StockWords : List Nat := projectDAGStock q1Mask qBase [0, 3, 6]
def q1Fact : (Nat × List Nat × Nat × Nat) := (q1Mask, q1StockWords, 4, q1Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q1Stock : Lower q1Mask q1StockWords q1Goal 4 := dagShiftLower (width := 256) (moveSchedule qStages [3]) q0Stock (by decide +kernel)
def q2Mask : Nat := 0x500050000000000050005
abbrev q2Goal : Nat := qGoal &&& q2Mask
abbrev q2StockWords : List Nat := projectDAGStock q2Mask qBase [1, 4, 6]
def q2Fact : (Nat × List Nat × Nat × Nat) := (q2Mask, q2StockWords, 4, q2Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q2Stock : Lower q2Mask q2StockWords q2Goal 4 := dagShiftLower (width := 256) (moveSchedule qStages [4, 5, 3]) q0Stock (by decide +kernel)
def q3Mask : Nat := 0x30300000000000000000000000000000303
abbrev q3Goal : Nat := qGoal &&& q3Mask
abbrev q3StockWords : List Nat := projectDAGStock q3Mask qBase [0, 3, 7]
def q3Fact : (Nat × List Nat × Nat × Nat) := (q3Mask, q3StockWords, 4, q3Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q3Stock : Lower q3Mask q3StockWords q3Goal 4 := dagShiftLower (width := 256) (moveSchedule qStages [6, 7]) q0Stock (by decide +kernel)
def q4Mask : Nat := 0x30000000300000000000000000000000300000003
abbrev q4Goal : Nat := qGoal &&& q4Mask
abbrev q4StockWords : List Nat := projectDAGStock q4Mask qBase [0, 5, 7]
def q4Fact : (Nat × List Nat × Nat × Nat) := (q4Mask, q4StockWords, 4, q4Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q4Stock : Lower q4Mask q4StockWords q4Goal 4 := dagShiftLower (width := 256) (moveSchedule qStages [0, 8, 6, 7]) q0Stock (by decide +kernel)
def q5Mask : Nat := 0x50000000500000000000000000000000500000005
abbrev q5Goal : Nat := qGoal &&& q5Mask
abbrev q5StockWords : List Nat := projectDAGStock q5Mask qBase [1, 5, 7]
def q5Fact : (Nat × List Nat × Nat × Nat) := (q5Mask, q5StockWords, 4, q5Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q5Stock : Lower q5Mask q5StockWords q5Goal 4 := dagShiftLower (width := 256) (moveSchedule qStages [4, 0, 8, 6, 7]) q0Stock (by decide +kernel)
def q6Mask : Nat := 0x1010000010100000000000000000000010100000101
abbrev q6Goal : Nat := qGoal &&& q6Mask
abbrev q6StockWords : List Nat := projectDAGStock q6Mask qBase [3, 5, 7]
def q6Fact : (Nat × List Nat × Nat × Nat) := (q6Mask, q6StockWords, 4, q6Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q6Stock : Lower q6Mask q6StockWords q6Goal 4 := dagShiftLower (width := 256) (moveSchedule qStages [1, 9, 10, 0, 8, 6, 7]) q0Stock (by decide +kernel)
def q7Mask : Nat := 0x303000003030
abbrev q7Goal : Nat := qGoal &&& q7Mask
abbrev q7StockWords : List Nat := projectDAGStock q7Mask qBase [0, 3, 5]
def q7Fact : (Nat × List Nat × Nat × Nat) := (q7Mask, q7StockWords, 4, q7Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q7Stock : Lower q7Mask q7StockWords q7Goal 4 := dagShiftLower (width := 256) (moveSchedule qStages [11]) q0Stock (by decide +kernel)
def q8Mask : Nat := 0x303000003030000
abbrev q8Goal : Nat := qGoal &&& q8Mask
abbrev q8StockWords : List Nat := projectDAGStock q8Mask qBase [0, 3, 5]
def q8Fact : (Nat × List Nat × Nat × Nat) := (q8Mask, q8StockWords, 4, q8Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q8Stock : Lower q8Mask q8StockWords q8Goal 4 := dagShiftLower (width := 256) (moveSchedule qStages [12]) q0Stock (by decide +kernel)
def q9Mask : Nat := 0x30300000000000003030
abbrev q9Goal : Nat := qGoal &&& q9Mask
abbrev q9StockWords : List Nat := projectDAGStock q9Mask qBase [0, 3, 6]
def q9Fact : (Nat × List Nat × Nat × Nat) := (q9Mask, q9StockWords, 4, q9Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q9Stock : Lower q9Mask q9StockWords q9Goal 4 := dagShiftLower (width := 256) (moveSchedule qStages [11, 3]) q0Stock (by decide +kernel)
def q10Mask : Nat := 0x303000000000000000000000000000003030000
abbrev q10Goal : Nat := qGoal &&& q10Mask
abbrev q10StockWords : List Nat := projectDAGStock q10Mask qBase [0, 3, 7]
def q10Fact : (Nat × List Nat × Nat × Nat) := (q10Mask, q10StockWords, 4, q10Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q10Stock : Lower q10Mask q10StockWords q10Goal 4 := dagShiftLower (width := 256) (moveSchedule qStages [12, 6, 7]) q0Stock (by decide +kernel)
def q11Mask : Nat := 0x300000003000000000000000000000003000000030000
abbrev q11Goal : Nat := qGoal &&& q11Mask
abbrev q11StockWords : List Nat := projectDAGStock q11Mask qBase [0, 5, 7]
def q11Fact : (Nat × List Nat × Nat × Nat) := (q11Mask, q11StockWords, 4, q11Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q11Stock : Lower q11Mask q11StockWords q11Goal 4 := dagShiftLower (width := 256) (moveSchedule qStages [12, 0, 8, 6, 7]) q0Stock (by decide +kernel)
def q12Mask : Nat := 0x3030000030300000000000000000000030300000303
abbrev q12Goal : Nat := qGoal &&& q12Mask
abbrev q12StockWords : List Nat := projectDAGStock q12Mask qBase [0, 3, 5, 7]
def q12Fact : (Nat × List Nat × Nat × Nat) := (q12Mask, q12StockWords, 7, q12Goal)
def q12Cuts : List (Nat × List Nat × Nat × Nat) := [q0Fact, q3Fact, q4Fact, q6Fact]
def q12Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 33, 40, 129, 136, 160, 9, 9, 9, 9, 9, 9, 1, 8, 32, 128, 1, 1, 1, 1, 1, 1, 1, 1], rfl⟩
def q12Sample : (Nat × Nat) := (0x4028040a040221008100a041088008841028040240209100a04021, 12)
def q12Witnesses := unpackWitnesses q12StockWords [66176, 331904, 606336, 868384]
def q12Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x4c24320722cc3401 0x501c3c3363432a0c0360402a1b92c13620033144992c8262b416206a32b6231f313141a02b1201f02013010080000f 9 4 12 3 5 5
def q12Data : (Nat → Nat × Nat) := fun i => decodeNode 3 15 0x728153314402640208078 i
def q12Tags := dagTraceTags q12Mask 12 (dagTagBases q12StockWords 0xfc0c3325e1ad 0xb004030580a4 12) 6 q12Data
def q12States := dagTrace q12Mask q12StockWords 6 q12Data
def q12Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q12Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q12Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q12Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q12Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 7, 4, 3, 6, 5] 0 i.val)
def q12Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 7, 6, 3] 0 i.val)
def q12Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 7, 6, 3] 0 i.val)
def q12Move3Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 7, 4, 3, 6, 5] 0 i.val)
def q12Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 7, 4, 5, 6, 3] 0 i.val)
def q12Move4Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 7, 4, 5, 6, 3] 0 i.val)
def q12Move5Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q12Move5Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q12Move6Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q12Move6Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q12Move7Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q12Move7Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q12Move8Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 1, 2, 0, 4, 3, 6, 5] 0 i.val)
def q12Move8Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 7, 6, 0] 0 i.val)
def q12Move9Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 7, 6, 3] 0 i.val)
def q12Move9Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 7, 4, 0, 6, 5] 0 i.val)
def q12Move10Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 1, 2, 0, 4, 5, 6, 3] 0 i.val)
def q12Move10Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 7, 4, 5, 6, 0] 0 i.val)
def q12Move11Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q12Move11Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q12Move12Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 7, 4, 0, 6, 5] 0 i.val)
def q12Move12Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 7, 6, 3] 0 i.val)
def q12Move13Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q12Move13Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q12Move14Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 1, 2, 3, 4, 0, 6, 5] 0 i.val)
def q12Move14Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 7, 6, 0] 0 i.val)
def q12Move15Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 7, 4, 0, 6, 3] 0 i.val)
def q12Move15Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 7, 4, 0, 6, 3] 0 i.val)
def q12MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [6]), q12Move0Map, q12Move0Inverse), ((moveSchedule qStages [0]), q12Move1Map, q12Move1Inverse), ((moveSchedule qStages [13, 6]), q12Move2Map, q12Move2Inverse), ((moveSchedule qStages [0, 6]), q12Move3Map, q12Move3Inverse), ((moveSchedule qStages [13]), q12Move4Map, q12Move4Inverse), ((moveSchedule qStages [1]), q12Move5Map, q12Move5Inverse), ((moveSchedule qStages [1, 6]), q12Move6Map, q12Move6Inverse), ((moveSchedule qStages [2, 0]), q12Move7Map, q12Move7Inverse), ((moveSchedule qStages [14, 13, 6]), q12Move8Map, q12Move8Inverse), ((moveSchedule qStages [2, 0, 6]), q12Move9Map, q12Move9Inverse), ((moveSchedule qStages [14, 13]), q12Move10Map, q12Move10Inverse), ((moveSchedule qStages [1, 0]), q12Move11Map, q12Move11Inverse), ((moveSchedule qStages [1, 13, 6]), q12Move12Map, q12Move12Inverse), ((moveSchedule qStages [2]), q12Move13Map, q12Move13Inverse), ((moveSchedule qStages [14, 6]), q12Move14Map, q12Move14Inverse), ((moveSchedule qStages [2, 13]), q12Move15Map, q12Move15Inverse)]
def q12Moves := dagMoves q12MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q12Autos : DagMovesOK q12Mask q12Goal 256 q12Moves := dagMovesOfCheck (by decide +kernel)
def q12Check := dagCheckNode q12Mask q12Goal q12Chart (dagKnownCloses q12Goal q12Cuts) 6 q12States q12Moves q12Links q12Sample q12Tags
def q12RootAt (token : Nat) : Bool :=
  let s := rootState q12StockWords 6 token
  !dagAllowedRoot q12Witnesses s.2.1 || dagLocal q12Mask q12Goal q12Chart (dagKnownCloses q12Goal q12Cuts) s ||
  dagRef 6 q12States q12Moves q12Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q12RootBlock0 : treeBlock 0 16 q12RootAt = true := by decide +kernel
theorem q12Roots : dagCheckRoots q12Mask q12Goal q12Chart (dagKnownCloses q12Goal q12Cuts) q12Witnesses (dagRef 6 q12States q12Moves q12Links 0) q12StockWords 6 = true := q12RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q12Block0 : treeBlock 0 6 q12Check = true := by decide +kernel
theorem q12Blocks : treeBlock 0 6 q12Check = true := q12Block0
theorem q12Known : Known q12Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q6Stock) q4Stock) q3Stock) q0Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q12Stock : Lower q12Mask q12StockWords q12Goal 7 := by
  apply lowerDag _ _ _ _ q12Autos _ _ _ q12Known _ q12Roots q12Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q12StockWords; decide +kernel
  · decide +kernel
  · simp only [q12Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def q13Mask : Nat := 0x30300000303000000000000000000000303000003030000
abbrev q13Goal : Nat := qGoal &&& q13Mask
abbrev q13StockWords : List Nat := projectDAGStock q13Mask qBase [0, 3, 5, 7]
def q13Fact : (Nat × List Nat × Nat × Nat) := (q13Mask, q13StockWords, 7, q13Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q13Stock : Lower q13Mask q13StockWords q13Goal 7 := dagShiftLower (width := 256) (moveSchedule qStages [12]) q12Stock (by decide +kernel)
def q14Mask : Nat := 0xf0f0f0f0f0f0f0f
abbrev q14Goal : Nat := qGoal &&& q14Mask
abbrev q14StockWords : List Nat := projectDAGStock q14Mask qBase [0, 1, 3, 4, 5]
def q14Fact : (Nat × List Nat × Nat × Nat) := (q14Mask, q14StockWords, 7, q14Goal)
def q14Cuts : List (Nat × List Nat × Nat × Nat) := [q8Fact]
def q14Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 18, 33, 34, 40, 9, 9, 9, 9, 9, 9, 9, 3, 10, 17, 24, 48, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def q14Sample : (Nat × Nat) := (0x223108884102808864141a08824402218088301a0182c06090088404220c06406130c024041200824402810084140b0884c1009080481409, 25)
def q14Witnesses := unpackWitnesses q14StockWords [25136, 287792, 553008, 799754, 1077272]
def q14Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x840e1 0x58715880804001f 5 2 12 2 1 3
def q14Data : (Nat → Nat × Nat) := fun i => decodeNode 2 14 0x30e1008407c i
def q14Tags := dagTraceTags q14Mask 25 (dagTagBases q14StockWords 0x1c630609886851e72b542f2a35a8eebd 0x60060d58505144285421aa23a8e488 25) 6 q14Data
def q14States := dagTrace q14Mask q14StockWords 6 q14Data
def q14Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q14Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q14MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [1]), q14Move0Map, q14Move0Inverse)]
def q14Moves := dagMoves q14MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q14Autos : DagMovesOK q14Mask q14Goal 256 q14Moves := dagMovesOfCheck (by decide +kernel)
def q14Check := dagCheckNode q14Mask q14Goal q14Chart (dagKnownCloses q14Goal q14Cuts) 3 q14States q14Moves q14Links q14Sample q14Tags
def q14RootAt (token : Nat) : Bool :=
  let s := rootState q14StockWords 6 token
  !dagAllowedRoot q14Witnesses s.2.1 || dagLocal q14Mask q14Goal q14Chart (dagKnownCloses q14Goal q14Cuts) s ||
  dagRef 3 q14States q14Moves q14Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q14RootBlock0 : treeBlock 0 32 q14RootAt = true := by decide +kernel
theorem q14Roots : dagCheckRoots q14Mask q14Goal q14Chart (dagKnownCloses q14Goal q14Cuts) q14Witnesses (dagRef 3 q14States q14Moves q14Links 0) q14StockWords 6 = true := q14RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q14Block0 : treeBlock 0 3 q14Check = true := by decide +kernel
theorem q14Blocks : treeBlock 0 3 q14Check = true := q14Block0
theorem q14Known : Known q14Cuts := extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q8Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q14Stock : Lower q14Mask q14StockWords q14Goal 7 := by
  apply lowerDag _ _ _ _ q14Autos _ _ _ q14Known _ q14Roots q14Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q14StockWords; decide +kernel
  · decide +kernel
  · simp only [q14Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def q15Mask : Nat := 0xf0f0f0f000000000f0f0f0f
abbrev q15Goal : Nat := qGoal &&& q15Mask
abbrev q15StockWords : List Nat := projectDAGStock q15Mask qBase [0, 1, 3, 4, 6]
def q15Fact : (Nat × List Nat × Nat × Nat) := (q15Mask, q15StockWords, 8, q15Goal)
def q15Cuts : List (Nat × List Nat × Nat × Nat) := [q1Fact, q2Fact]
def q15Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 18, 65, 66, 72, 80, 9, 9, 9, 9, 9, 9, 3, 10, 17, 24, 64, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def q15Sample : (Nat × Nat) := (0x224101908221208140104808864141a08824805020108301a0182c06090090404420c06406130c024041200824804820104140b0884c1009080481409, 27)
def q15Witnesses := unpackWitnesses q15StockWords [33344, 296000, 561216, 827456, 1093656]
def q15Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x160b05824920903cc3c01 0x7f0e2792c5d88073141f0e0e92c18c505c39130e1b937664b23637a98ae16204ccde231f44c503037280ac201304020001f 9 4 12 3 3 5
def q15Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0xc3823142c391c38103710131008101f0 i
def q15Tags := dagTraceTags q15Mask 27 (dagTagBases q15StockWords 0x6c6306036a1a141e72b5589ca8d428eebd 0x60060b5214141442855086a88f28e488 27) 7 q15Data
def q15States := dagTrace q15Mask q15StockWords 7 q15Data
def q15Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q15Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 4, 2, 3, 1, 5, 6, 7] 0 i.val)
def q15Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 4, 3, 5, 6, 7] 0 i.val)
def q15Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 4, 3, 5, 6, 7] 0 i.val)
def q15Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 0, 2, 1, 3, 5, 6, 7] 0 i.val)
def q15Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 3, 2, 4, 0, 5, 6, 7] 0 i.val)
def q15Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q15Move3Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q15Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 4, 2, 0, 1, 5, 6, 7] 0 i.val)
def q15Move4Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 4, 2, 0, 1, 5, 6, 7] 0 i.val)
def q15Move5Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 3, 2, 4, 0, 5, 6, 7] 0 i.val)
def q15Move5Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 0, 2, 1, 3, 5, 6, 7] 0 i.val)
def q15Move6Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 5, 6, 7] 0 i.val)
def q15Move6Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 5, 6, 7] 0 i.val)
def q15MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [15]), q15Move0Map, q15Move0Inverse), ((moveSchedule qStages [4, 5]), q15Move1Map, q15Move1Inverse), ((moveSchedule qStages [16, 15, 5]), q15Move2Map, q15Move2Inverse), ((moveSchedule qStages [1]), q15Move3Map, q15Move3Inverse), ((moveSchedule qStages [1, 15]), q15Move4Map, q15Move4Inverse), ((moveSchedule qStages [4, 9, 5]), q15Move5Map, q15Move5Inverse), ((moveSchedule qStages [16, 9]), q15Move6Map, q15Move6Inverse)]
def q15Moves := dagMoves q15MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q15Autos : DagMovesOK q15Mask q15Goal 256 q15Moves := dagMovesOfCheck (by decide +kernel)
def q15Check := dagCheckNode q15Mask q15Goal q15Chart (dagKnownCloses q15Goal q15Cuts) 8 q15States q15Moves q15Links q15Sample q15Tags
def q15RootAt (token : Nat) : Bool :=
  let s := rootState q15StockWords 7 token
  !dagAllowedRoot q15Witnesses s.2.1 || dagLocal q15Mask q15Goal q15Chart (dagKnownCloses q15Goal q15Cuts) s ||
  dagRef 8 q15States q15Moves q15Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q15RootBlock0 : treeBlock 0 32 q15RootAt = true := by decide +kernel
theorem q15Roots : dagCheckRoots q15Mask q15Goal q15Chart (dagKnownCloses q15Goal q15Cuts) q15Witnesses (dagRef 8 q15States q15Moves q15Links 0) q15StockWords 7 = true := q15RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q15Block0 : treeBlock 0 8 q15Check = true := by decide +kernel
theorem q15Blocks : treeBlock 0 8 q15Check = true := q15Block0
theorem q15Known : Known q15Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q2Stock) q1Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q15Stock : Lower q15Mask q15StockWords q15Goal 8 := by
  apply lowerDag _ _ _ _ q15Autos _ _ _ q15Known _ q15Roots q15Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q15StockWords; decide +kernel
  · decide +kernel
  · simp only [q15Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def q16Mask : Nat := 0x3030303030303030303030303030303
abbrev q16Goal : Nat := qGoal &&& q16Mask
abbrev q16StockWords : List Nat := projectDAGStock q16Mask qBase [0, 3, 4, 5, 6]
def q16Cuts : List (Nat × List Nat × Nat × Nat) := [q1Fact, q8Fact]
def q16Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 33, 40, 65, 72, 80, 9, 9, 9, 9, 9, 9, 17, 24, 48, 96, 17, 17, 17, 17, 17, 17, 17, 17], rfl⟩
def q16Sample : (Nat × Nat) := (0x181c0605008140c070088c4222120120221908824804100904c021041200221040a030190c0248050040240209100a04021, 22)
def q16Witnesses := unpackWitnesses q16StockWords [49760, 315488, 581728, 815128, 1105968]
def q16Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x840e1 0xb8a204c81001f 5 2 10 2 1 3
def q16Data : (Nat → Nat × Nat) := fun i => decodeNode 2 12 0x4d02107c i
def q16Tags := dagTraceTags q16Mask 22 (dagTagBases q16StockWords 0x3c9a109c160fe4050038bb837d6d 0x49410d0100fb6060000ba036904 22) 6 q16Data
def q16States := dagTrace q16Mask q16StockWords 6 q16Data
def q16Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q16Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q16MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [1]), q16Move0Map, q16Move0Inverse)]
def q16Moves := dagMoves q16MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q16Autos : DagMovesOK q16Mask q16Goal 256 q16Moves := dagMovesOfCheck (by decide +kernel)
def q16Check := dagCheckNode q16Mask q16Goal q16Chart (dagKnownCloses q16Goal q16Cuts) 3 q16States q16Moves q16Links q16Sample q16Tags
def q16RootAt (token : Nat) : Bool :=
  let s := rootState q16StockWords 6 token
  !dagAllowedRoot q16Witnesses s.2.1 || dagLocal q16Mask q16Goal q16Chart (dagKnownCloses q16Goal q16Cuts) s ||
  dagRef 3 q16States q16Moves q16Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q16RootBlock0 : treeBlock 0 32 q16RootAt = true := by decide +kernel
theorem q16Roots : dagCheckRoots q16Mask q16Goal q16Chart (dagKnownCloses q16Goal q16Cuts) q16Witnesses (dagRef 3 q16States q16Moves q16Links 0) q16StockWords 6 = true := q16RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q16Block0 : treeBlock 0 3 q16Check = true := by decide +kernel
theorem q16Blocks : treeBlock 0 3 q16Check = true := q16Block0
theorem q16Known : Known q16Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q8Stock) q1Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q16Stock : Lower q16Mask q16StockWords q16Goal 7 := by
  apply lowerDag _ _ _ _ q16Autos _ _ _ q16Known _ q16Roots q16Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q16StockWords; decide +kernel
  · decide +kernel
  · simp only [q16Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def q17Mask : Nat := 0x330033000000000033003300000000003300330000000000330033
abbrev q17Goal : Nat := qGoal &&& q17Mask
abbrev q17StockWords : List Nat := projectDAGStock q17Mask qBase [0, 2, 4, 6, 7]
def q17Fact : (Nat × List Nat × Nat × Nat) := (q17Mask, q17StockWords, 7, q17Goal)
def q17Cuts : List (Nat × List Nat × Nat × Nat) := []
def q17Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[20, 65, 80, 129, 132, 20, 20, 20, 20, 20, 20, 20, 5, 17, 68, 144, 192, 5, 5, 5, 5, 5, 5, 5], rfl⟩
def q17Sample : (Nat × Nat) := (0x120d02231120506034022916014180c4029140a41402108050221400281022100241081412091028540a14020508845088548041080502214, 25)
def q17Witnesses := unpackWitnesses q17StockWords [99008, 362688, 630976, 893072, 1148996]
def q17Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x30341 0x1f870d92c3b1014c502010001f 6 3 12 1 4 4
def q17Data : (Nat → Nat × Nat) := fun i => decodeNode 2 14 0x8407c i
def q17Tags := dagTraceTags q17Mask 25 (dagTagBases q17StockWords 0x1b49900f7b30a5e18fad0d11f613159c 0x16c810056300a5400c2d0651e01314c9 25) 6 q17Data
def q17States := dagTrace q17Mask q17StockWords 6 q17Data
def q17Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 4, 3, 2, 5, 7, 6] 0 i.val)
def q17Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 4, 3, 2, 5, 7, 6] 0 i.val)
def q17Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 3, 6, 5, 4, 7] 0 i.val)
def q17Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 3, 6, 5, 4, 7] 0 i.val)
def q17Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 1, 0, 3, 7, 5, 2, 6] 0 i.val)
def q17Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 6, 3, 0, 5, 7, 4] 0 i.val)
def q17Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 6, 3, 0, 5, 7, 4] 0 i.val)
def q17Move3Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 1, 0, 3, 7, 5, 2, 6] 0 i.val)
def q17Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 1, 7, 3, 0, 5, 6, 2] 0 i.val)
def q17Move4Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 1, 7, 3, 0, 5, 6, 2] 0 i.val)
def q17Move5Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 1, 2, 3, 7, 5, 0, 4] 0 i.val)
def q17Move5Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 1, 2, 3, 7, 5, 0, 4] 0 i.val)
def q17Move6Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 1, 4, 3, 6, 5, 0, 2] 0 i.val)
def q17Move6Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 1, 7, 3, 2, 5, 4, 0] 0 i.val)
def q17Move7Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [6, 1, 7, 3, 2, 5, 4, 0] 0 i.val)
def q17Move7Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 1, 4, 3, 6, 5, 0, 2] 0 i.val)
def q17Move8Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 1, 6, 3, 4, 5, 2, 0] 0 i.val)
def q17Move8Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 1, 6, 3, 4, 5, 2, 0] 0 i.val)
def q17MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [17, 7]), q17Move0Map, q17Move0Inverse), ((moveSchedule qStages [18, 19]), q17Move1Map, q17Move1Inverse), ((moveSchedule qStages [16, 17, 20, 7]), q17Move2Map, q17Move2Inverse), ((moveSchedule qStages [18, 21, 19, 7]), q17Move3Map, q17Move3Inverse), ((moveSchedule qStages [16, 22]), q17Move4Map, q17Move4Inverse), ((moveSchedule qStages [23, 20]), q17Move5Map, q17Move5Inverse), ((moveSchedule qStages [14, 17, 19, 7]), q17Move6Map, q17Move6Inverse), ((moveSchedule qStages [23, 22, 20, 7]), q17Move7Map, q17Move7Inverse), ((moveSchedule qStages [14, 21]), q17Move8Map, q17Move8Inverse)]
def q17Moves := dagMoves q17MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q17Autos : DagMovesOK q17Mask q17Goal 256 q17Moves := dagMovesOfCheck (by decide +kernel)
def q17Check := dagCheckNode q17Mask q17Goal q17Chart (dagKnownCloses q17Goal q17Cuts) 2 q17States q17Moves q17Links q17Sample q17Tags
def q17RootAt (token : Nat) : Bool :=
  let s := rootState q17StockWords 6 token
  !dagAllowedRoot q17Witnesses s.2.1 || dagLocal q17Mask q17Goal q17Chart (dagKnownCloses q17Goal q17Cuts) s ||
  dagRef 2 q17States q17Moves q17Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q17RootBlock0 : treeBlock 0 32 q17RootAt = true := by decide +kernel
theorem q17Roots : dagCheckRoots q17Mask q17Goal q17Chart (dagKnownCloses q17Goal q17Cuts) q17Witnesses (dagRef 2 q17States q17Moves q17Links 0) q17StockWords 6 = true := q17RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q17Block0 : treeBlock 0 2 q17Check = true := by decide +kernel
theorem q17Blocks : treeBlock 0 2 q17Check = true := q17Block0
theorem q17Known : Known q17Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q17Stock : Lower q17Mask q17StockWords q17Goal 7 := by
  apply lowerDag _ _ _ _ q17Autos _ _ _ q17Known _ q17Roots q17Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q17StockWords; decide +kernel
  · decide +kernel
  · simp only [q17Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def q18Mask : Nat := 0x333333330000000033333333
abbrev q18Goal : Nat := qGoal &&& q18Mask
abbrev q18StockWords : List Nat := projectDAGStock q18Mask qBase [0, 2, 3, 4, 6]
def q18Fact : (Nat × List Nat × Nat × Nat) := (q18Mask, q18StockWords, 7, q18Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q18Stock : Lower q18Mask q18StockWords q18Goal 7 := dagShiftLower (width := 256) (moveSchedule qStages [15, 17, 3]) q14Stock (by decide +kernel)
def q19Mask : Nat := 0xf0f0f0f0000000000000000000000000f0f0f0f
abbrev q19Goal : Nat := qGoal &&& q19Mask
abbrev q19StockWords : List Nat := projectDAGStock q19Mask qBase [0, 1, 3, 4, 7]
def q19Fact : (Nat × List Nat × Nat × Nat) := (q19Mask, q19StockWords, 7, q19Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q19Stock : Lower q19Mask q19StockWords q19Goal 7 := dagShiftLower (width := 256) (moveSchedule qStages [6, 7]) q14Stock (by decide +kernel)
def q20Mask : Nat := 0x3333333300000000000000000000000033333333
abbrev q20Goal : Nat := qGoal &&& q20Mask
abbrev q20StockWords : List Nat := projectDAGStock q20Mask qBase [0, 2, 3, 4, 7]
def q20Fact : (Nat × List Nat × Nat × Nat) := (q20Mask, q20StockWords, 7, q20Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q20Stock : Lower q20Mask q20StockWords q20Goal 7 := dagShiftLower (width := 256) (moveSchedule qStages [24, 6, 7]) q14Stock (by decide +kernel)
def q21Mask : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
abbrev q21Goal : Nat := qGoal &&& q21Mask
abbrev q21StockWords : List Nat := projectDAGStock q21Mask qBase [0, 1, 4, 5, 7]
def q21Fact : (Nat × List Nat × Nat × Nat) := (q21Mask, q21StockWords, 7, q21Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q21Stock : Lower q21Mask q21StockWords q21Goal 7 := dagShiftLower (width := 256) (moveSchedule qStages [2, 24, 10, 13, 7]) q16Stock (by decide +kernel)
def q22Mask : Nat := 0x3300330033003300000000000000000033003300330033
abbrev q22Goal : Nat := qGoal &&& q22Mask
abbrev q22StockWords : List Nat := projectDAGStock q22Mask qBase [0, 2, 4, 5, 7]
def q22Fact : (Nat × List Nat × Nat × Nat) := (q22Mask, q22StockWords, 7, q22Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q22Stock : Lower q22Mask q22StockWords q22Goal 7 := dagShiftLower (width := 256) (moveSchedule qStages [24, 0, 6, 7]) q14Stock (by decide +kernel)
def q23Mask : Nat := 0x50505050505050500000000000000000505050505050505
abbrev q23Goal : Nat := qGoal &&& q23Mask
abbrev q23StockWords : List Nat := projectDAGStock q23Mask qBase [1, 3, 4, 5, 7]
def q23Fact : (Nat × List Nat × Nat × Nat) := (q23Mask, q23StockWords, 7, q23Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q23Stock : Lower q23Mask q23StockWords q23Goal 7 := dagShiftLower (width := 256) (moveSchedule qStages [2, 25, 13, 6, 7]) q16Stock (by decide +kernel)
def q24Mask : Nat := 0x111111111111111100000000000000001111111111111111
abbrev q24Goal : Nat := qGoal &&& q24Mask
abbrev q24StockWords : List Nat := projectDAGStock q24Mask qBase [2, 3, 4, 5, 7]
def q24Fact : (Nat × List Nat × Nat × Nat) := (q24Mask, q24StockWords, 7, q24Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q24Stock : Lower q24Mask q24StockWords q24Goal 7 := dagShiftLower (width := 256) (moveSchedule qStages [1, 24, 10, 0, 6, 7]) q14Stock (by decide +kernel)
def q25Mask : Nat := 0x3333000000000000333300000000000033330000000000003333
abbrev q25Goal : Nat := qGoal &&& q25Mask
abbrev q25StockWords : List Nat := projectDAGStock q25Mask qBase [0, 2, 3, 6, 7]
def q25Fact : (Nat × List Nat × Nat × Nat) := (q25Mask, q25StockWords, 7, q25Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q25Stock : Lower q25Mask q25StockWords q25Goal 7 := dagShiftLower (width := 256) (moveSchedule qStages [17, 3, 7]) q16Stock (by decide +kernel)
def q26Mask : Nat := 0x3030303000000000303030300000000030303030000000003030303
abbrev q26Goal : Nat := qGoal &&& q26Mask
abbrev q26StockWords : List Nat := projectDAGStock q26Mask qBase [0, 3, 4, 6, 7]
def q26Fact : (Nat × List Nat × Nat × Nat) := (q26Mask, q26StockWords, 7, q26Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q26Stock : Lower q26Mask q26StockWords q26Goal 7 := dagShiftLower (width := 256) (moveSchedule qStages [6]) q16Stock (by decide +kernel)
def q27Mask : Nat := 0x11111111000000001111111100000000111111110000000011111111
abbrev q27Goal : Nat := qGoal &&& q27Mask
abbrev q27StockWords : List Nat := projectDAGStock q27Mask qBase [2, 3, 4, 6, 7]
def q27Fact : (Nat × List Nat × Nat × Nat) := (q27Mask, q27StockWords, 7, q27Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q27Stock : Lower q27Mask q27StockWords q27Goal 7 := dagShiftLower (width := 256) (moveSchedule qStages [18, 24, 10, 19]) q17Stock (by decide +kernel)
def q28Mask : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
abbrev q28Goal : Nat := qGoal &&& q28Mask
abbrev q28StockWords : List Nat := projectDAGStock q28Mask qBase [0, 4, 5, 6, 7]
def q28Fact : (Nat × List Nat × Nat × Nat) := (q28Mask, q28StockWords, 7, q28Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q28Stock : Lower q28Mask q28StockWords q28Goal 7 := dagShiftLower (width := 256) (moveSchedule qStages [2, 26, 21, 13]) q14Stock (by decide +kernel)
def q29Mask : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
abbrev q29Goal : Nat := qGoal &&& q29Mask
abbrev q29StockWords : List Nat := projectDAGStock q29Mask qBase [1, 4, 5, 6, 7]
def q29Fact : (Nat × List Nat × Nat × Nat) := (q29Mask, q29StockWords, 8, q29Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q29Stock : Lower q29Mask q29StockWords q29Goal 8 := dagShiftLower (width := 256) (moveSchedule qStages [16, 25, 17, 27, 20, 6, 7]) q15Stock (by decide +kernel)
def q30Mask : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
abbrev q30Goal : Nat := qGoal &&& q30Mask
abbrev q30StockWords : List Nat := projectDAGStock q30Mask qBase [0, 1, 2, 4, 5, 7]
def q30Fact : (Nat × List Nat × Nat × Nat) := (q30Mask, q30StockWords, 9, q30Goal)
def q30Cuts : List (Nat × List Nat × Nat × Nat) := [q5Fact, q11Fact, q22Fact, q21Fact]
def q30Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[18, 20, 33, 34, 129, 130, 132, 160, 18, 18, 18, 18, 7, 17, 36, 48, 144, 7, 7, 7, 7, 7, 7, 7], rfl⟩
def q30Sample : (Nat × Nat) := (0x4828060a003a0406824820500a010280488408a442281120d02231120500884180d00a2518051008440208081412098482200a040482008850081010880622180c406130184804121209422150885020140884c4021080482212, 40)
def q30Witnesses := unpackWitnesses q30StockWords [74384, 337040, 600208, 813092, 1138832, 1400880]
def q30Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x2008020080200802008020080200801f16d1b060d80511133c8f03c0c306c01 0x4b1313f44430e0e3145c0c5663454cd140344fd111c423f0e0d3144b0e1192c300210f443f0e0ef44370e0c9422fd14af442710c8c3f1f0e46c3816508492c0c10c203704020003f 10 4 12 5 1 5
def q30Data : (Nat → Nat × Nat) := fun i => decodeNode 5 17 0x315b1a24cd120689f443e1c1a4b0de885c382fa20b0e052842f450fa20710c387e1c390e1c0650832581043081b84020207e0 i
def q30Tags := dagTraceTags q30Mask 40 (dagTagBases q30StockWords 0xffc4634000c6330cb88400ba900f7b012fd800f010002d370b28d102cccc 0x8c00604000432a8c0884c8d280087b212d1c0080300001370030d1029669 40) 8 q30Data
def q30States := dagTrace q30Mask q30StockWords 8 q30Data
def q30MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := []
def q30Moves := dagMoves q30MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q30Autos : DagMovesOK q30Mask q30Goal 256 q30Moves := dagMovesOfCheck (by decide +kernel)
def q30Check := dagCheckNode q30Mask q30Goal q30Chart (dagKnownCloses q30Goal q30Cuts) 24 q30States q30Moves q30Links q30Sample q30Tags
def q30RootAt (token : Nat) : Bool :=
  let s := rootState q30StockWords 8 token
  !dagAllowedRoot q30Witnesses s.2.1 || dagLocal q30Mask q30Goal q30Chart (dagKnownCloses q30Goal q30Cuts) s ||
  dagRef 24 q30States q30Moves q30Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q30RootBlock0 : treeBlock 0 64 q30RootAt = true := by decide +kernel
theorem q30Roots : dagCheckRoots q30Mask q30Goal q30Chart (dagKnownCloses q30Goal q30Cuts) q30Witnesses (dagRef 24 q30States q30Moves q30Links 0) q30StockWords 8 = true := q30RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q30Block0 : treeBlock 0 16 q30Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q30Block16 : treeBlock 16 8 q30Check = true := by decide +kernel
theorem q30Verified : treeBlock 0 24 q30Check = true := (@treeBlock_merge 0 16 8 q30Check q30Block0 q30Block16)
theorem q30Blocks : treeBlock 0 24 q30Check = true := q30Verified
theorem q30Known : Known q30Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q21Stock) q22Stock) q11Stock) q5Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q30Stock : Lower q30Mask q30StockWords q30Goal 9 := by
  apply lowerDag _ _ _ _ q30Autos _ _ _ q30Known _ q30Roots q30Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q30StockWords; decide +kernel
  · decide +kernel
  · simp only [q30Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def q31Mask : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
abbrev q31Goal : Nat := qGoal &&& q31Mask
abbrev q31StockWords : List Nat := projectDAGStock q31Mask qBase [0, 1, 3, 4, 5, 7]
def q31Fact : (Nat × List Nat × Nat × Nat) := (q31Mask, q31StockWords, 10, q31Goal)
def q31Cuts : List (Nat × List Nat × Nat × Nat) := [q12Fact, q5Fact, q14Fact, q13Fact, q19Fact, q21Fact, q23Fact]
def q31Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 18, 33, 34, 40, 129, 130, 136, 160, 9, 9, 9, 3, 10, 17, 24, 48, 144, 3, 3, 3, 3, 3, 3], rfl⟩
def q31Sample : (Nat × Nat) := (0x602801a09208101a0430280508860b01828120b04828006230188860314028040a008a442281088c4222140220108805208102808864141a0882500821008860220c068060b01825008100a0404820088404220c06406130c024041200824402810084140b0884c1009080481409, 49)
def q31Witnesses := unpackWitnesses q31StockWords [74384, 337040, 602256, 799754, 1138832, 1400880]
def q31Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0xfc3f0fc3f0fc3f0f4bd0f43d0f07b1e87a0e83a0e4790dcb70d4a9c8d9a9464b606801 0xb0c3830620340403201c349403233430f442e92c6ef442ec382d250aa64fa464de0641a0635926202a04f2404d60041200351a01f1200828f44e69439092c663431832b103142725024f4e22f4420c4e166411e6358e6201c04e1401e592501af4f18f445694e16942d464e946425404e1404250f4412c4310c384e6430e6370c62048f440ac4308c38c6643866378262046043060370401f020080003f 10 4 13 5 2 5
def q31Data : (Nat → Nat × Nat) := fun i => decodeNode 5 18 0x1280f19a2de88961c1e4a0602799e88592811e9c47a21189c431a9009c47a78de8834a10c084362189870231b88c40262185870101b8403e10040407e0 i
def q31Tags := dagTraceTags q31Mask 49 (dagTagBases q31StockWords 0x1cf1e708380011ffcc430306002894184068544000de382b5510c012f8aa346053c287aebd 0x831040820001061400300060abc9e14c0505060007420285550c0120caa22a063c286a488 49) 9 q31Data
def q31States := dagTrace q31Mask q31StockWords 9 q31Data
def q31Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q31Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q31Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q31Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q31Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q31Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q31MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [6]), q31Move0Map, q31Move0Inverse), ((moveSchedule qStages [1]), q31Move1Map, q31Move1Inverse), ((moveSchedule qStages [1, 6]), q31Move2Map, q31Move2Inverse)]
def q31Moves := dagMoves q31MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q31Autos : DagMovesOK q31Mask q31Goal 256 q31Moves := dagMovesOfCheck (by decide +kernel)
def q31Check := dagCheckNode q31Mask q31Goal q31Chart (dagKnownCloses q31Goal q31Cuts) 27 q31States q31Moves q31Links q31Sample q31Tags
def q31RootAt (token : Nat) : Bool :=
  let s := rootState q31StockWords 9 token
  !dagAllowedRoot q31Witnesses s.2.1 || dagLocal q31Mask q31Goal q31Chart (dagKnownCloses q31Goal q31Cuts) s ||
  dagRef 27 q31States q31Moves q31Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q31RootBlock0 : treeBlock 0 64 q31RootAt = true := by decide +kernel
theorem q31Roots : dagCheckRoots q31Mask q31Goal q31Chart (dagKnownCloses q31Goal q31Cuts) q31Witnesses (dagRef 27 q31States q31Moves q31Links 0) q31StockWords 9 = true := q31RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q31Block0 : treeBlock 0 16 q31Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q31Block16 : treeBlock 16 11 q31Check = true := by decide +kernel
theorem q31Verified : treeBlock 0 27 q31Check = true := (@treeBlock_merge 0 16 11 q31Check q31Block0 q31Block16)
theorem q31Blocks : treeBlock 0 27 q31Check = true := q31Verified
theorem q31Known : Known q31Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q23Stock) q21Stock) q19Stock) q13Stock) q14Stock) q5Stock) q12Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q31Stock : Lower q31Mask q31StockWords q31Goal 10 := by
  apply lowerDag _ _ _ _ q31Autos _ _ _ q31Known _ q31Roots q31Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q31StockWords; decide +kernel
  · decide +kernel
  · simp only [q31Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def q32Mask : Nat := 0x333333333333333300000000000000003333333333333333
abbrev q32Goal : Nat := qGoal &&& q32Mask
abbrev q32StockWords : List Nat := projectDAGStock q32Mask qBase [0, 2, 3, 4, 5, 7]
def q32Fact : (Nat × List Nat × Nat × Nat) := (q32Mask, q32StockWords, 10, q32Goal)
def q32Cuts : List (Nat × List Nat × Nat × Nat) := [q12Fact, q22Fact, q24Fact, q13Fact, q20Fact, q7Fact]
def q32Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 20, 33, 40, 129, 132, 136, 160, 9, 9, 9, 9, 5, 12, 17, 24, 36, 48, 144, 5, 5, 5, 5, 5], rfl⟩
def q32Sample : (Nat × Nat) := (0x1200948220602112084308802a140a844824500a010280488408a442281120d0223112051008804220188408864181c0882460340289460144021120840c0700a0d02825008100a0408840088410280c0640a150c024081400824402810084180d088541009080501809, 47)
def q32Witnesses := unpackWitnesses q32StockWords [74384, 338064, 602256, 813092, 1138832, 1400880]
def q32Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x3d0f43d0f43d0f43d0f07b1ec3b0ec3b0e4b81e0362d8360d0ae6a19cc4e4c706c01 0x3201c1800e0c8d08606802e334367a20b24b059e882ac38737a6b53d114d29a9492c131a6850c51a5e892094349496180d0c40656123141492809bd10bd89a64c4331620b430e03cc9a2464311320a41880b006c1801e1092833bd103d29c1c9420d4962619392cc841804e0b021053d1425e8850c432661c04190c1cc6e0c620057a2823d118d886c2c3843321c118dd04c40060432201b81007c040100003f 10 4 13 5 3 5
def q32Data : (Nat → Nat × Nat) := fun i => decodeNode 5 18 0x1a134680d19a31e88761c1e4a047a210c864320924a034a70d28434960c09c30210de8a27a208c86231b88c4027a285e8810218403e10040407e0 i
def q32Tags := dagTraceTags q32Mask 47 (dagTagBases q32StockWords 0x13fe3818e00018630180306001171a901a159001b8386b541894afe228d5a8d0a87aebd 0x306020188000183281400060e91a16b014141000d02068545894a432288830d0a86a488 47) 9 q32Data
def q32States := dagTrace q32Mask q32StockWords 9 q32Data
def q32Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q32Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 5, 4, 3, 6, 7] 0 i.val)
def q32Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q32Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q32Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q32Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q32Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 5, 4, 0, 6, 7] 0 i.val)
def q32Move3Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 0, 4, 3, 6, 7] 0 i.val)
def q32Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q32Move4Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 1, 2, 3, 4, 0, 6, 7] 0 i.val)
def q32MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [0]), q32Move0Map, q32Move0Inverse), ((moveSchedule qStages [1]), q32Move1Map, q32Move1Inverse), ((moveSchedule qStages [2, 0]), q32Move2Map, q32Move2Inverse), ((moveSchedule qStages [1, 0]), q32Move3Map, q32Move3Inverse), ((moveSchedule qStages [2]), q32Move4Map, q32Move4Inverse)]
def q32Moves := dagMoves q32MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q32Autos : DagMovesOK q32Mask q32Goal 256 q32Moves := dagMovesOfCheck (by decide +kernel)
def q32Check := dagCheckNode q32Mask q32Goal q32Chart (dagKnownCloses q32Goal q32Cuts) 26 q32States q32Moves q32Links q32Sample q32Tags
def q32RootAt (token : Nat) : Bool :=
  let s := rootState q32StockWords 9 token
  !dagAllowedRoot q32Witnesses s.2.1 || dagLocal q32Mask q32Goal q32Chart (dagKnownCloses q32Goal q32Cuts) s ||
  dagRef 26 q32States q32Moves q32Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q32RootBlock0 : treeBlock 0 64 q32RootAt = true := by decide +kernel
theorem q32Roots : dagCheckRoots q32Mask q32Goal q32Chart (dagKnownCloses q32Goal q32Cuts) q32Witnesses (dagRef 26 q32States q32Moves q32Links 0) q32StockWords 9 = true := q32RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q32Block0 : treeBlock 0 16 q32Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q32Block16 : treeBlock 16 10 q32Check = true := by decide +kernel
theorem q32Verified : treeBlock 0 26 q32Check = true := (@treeBlock_merge 0 16 10 q32Check q32Block0 q32Block16)
theorem q32Blocks : treeBlock 0 26 q32Check = true := q32Verified
theorem q32Known : Known q32Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q7Stock) q20Stock) q13Stock) q24Stock) q22Stock) q12Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q32Stock : Lower q32Mask q32StockWords q32Goal 10 := by
  apply lowerDag _ _ _ _ q32Autos _ _ _ q32Known _ q32Roots q32Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q32StockWords; decide +kernel
  · decide +kernel
  · simp only [q32Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def q33Mask : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
abbrev q33Goal : Nat := qGoal &&& q33Mask
abbrev q33StockWords : List Nat := projectDAGStock q33Mask qBase [0, 1, 2, 4, 6, 7]
def q33Fact : (Nat × List Nat × Nat × Nat) := (q33Mask, q33StockWords, 9, q33Goal)
def q33Cuts : List (Nat × List Nat × Nat × Nat) := [q2Fact, q17Fact]
def q33Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[18, 20, 65, 66, 80, 129, 130, 132, 18, 18, 18, 18, 7, 17, 68, 144, 192, 7, 7, 7, 7, 7, 7, 7], rfl⟩
def q33Sample : (Nat × Nat) := (0x2221022814020422416020406420385120814834088c44814180d008a458050201402050220500884603100a4502905008440208081422118884200a0404820090404424824406130184804122211422150885020140884c8041080482212, 42)
def q33Witnesses := unpackWitnesses q33StockWords [99008, 361664, 624832, 893120, 1155216, 1411140]
def q33Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x743a1d0e8743a1d0e86cb43a0b25824920904083e01 0x2df44370e11c4142532e6283cca0e02837d10cc38ae4b0a3142f0e0a92c27d128c43970e64c382250c79371a4cc592d124b226378d8ae16200c0dc202b04020003f 9 4 12 5 1 5
def q33Data : (Nat → Nat × Nat) := fun i => decodeNode 5 17 0x31053298732838141fd10b8705c3814960bd10328619370c99864b432581037081584020207e0 i
def q33Tags := dagTraceTags q33Mask 42 (dagTagBases q33StockWords 0xe9d8663200053dce3308402bf8103dee0903d600f0040002d5c2de42060accc 0x29b42602002215a83008451a900021ee090367008006000015c01582060a669 42) 8 q33Data
def q33States := dagTrace q33Mask q33StockWords 8 q33Data
def q33Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 3, 6, 5, 4, 7] 0 i.val)
def q33Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [2, 1, 0, 3, 6, 5, 4, 7] 0 i.val)
def q33MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [18, 19]), q33Move0Map, q33Move0Inverse)]
def q33Moves := dagMoves q33MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q33Autos : DagMovesOK q33Mask q33Goal 256 q33Moves := dagMovesOfCheck (by decide +kernel)
def q33Check := dagCheckNode q33Mask q33Goal q33Chart (dagKnownCloses q33Goal q33Cuts) 18 q33States q33Moves q33Links q33Sample q33Tags
def q33RootAt (token : Nat) : Bool :=
  let s := rootState q33StockWords 8 token
  !dagAllowedRoot q33Witnesses s.2.1 || dagLocal q33Mask q33Goal q33Chart (dagKnownCloses q33Goal q33Cuts) s ||
  dagRef 18 q33States q33Moves q33Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q33RootBlock0 : treeBlock 0 64 q33RootAt = true := by decide +kernel
theorem q33Roots : dagCheckRoots q33Mask q33Goal q33Chart (dagKnownCloses q33Goal q33Cuts) q33Witnesses (dagRef 18 q33States q33Moves q33Links 0) q33StockWords 8 = true := q33RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q33Block0 : treeBlock 0 16 q33Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q33Block16 : treeBlock 16 2 q33Check = true := by decide +kernel
theorem q33Verified : treeBlock 0 18 q33Check = true := (@treeBlock_merge 0 16 2 q33Check q33Block0 q33Block16)
theorem q33Blocks : treeBlock 0 18 q33Check = true := q33Verified
theorem q33Known : Known q33Cuts := extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q17Stock) q2Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q33Stock : Lower q33Mask q33StockWords q33Goal 9 := by
  apply lowerDag _ _ _ _ q33Autos _ _ _ q33Known _ q33Roots q33Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q33StockWords; decide +kernel
  · decide +kernel
  · simp only [q33Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def q34Mask : Nat := 0x33333333000000003333333300000000333333330000000033333333
abbrev q34Goal : Nat := qGoal &&& q34Mask
abbrev q34StockWords : List Nat := projectDAGStock q34Mask qBase [0, 2, 3, 4, 6, 7]
def q34Fact : (Nat × List Nat × Nat × Nat) := (q34Mask, q34StockWords, 10, q34Goal)
def q34Cuts : List (Nat × List Nat × Nat × Nat) := [q3Fact, q9Fact, q17Fact, q27Fact, q18Fact, q10Fact, q20Fact, q25Fact, q26Fact]
def q34Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 20, 65, 72, 80, 129, 132, 136, 9, 9, 9, 9, 5, 12, 17, 24, 68, 144, 192, 5, 5, 5, 5, 5], rfl⟩
def q34Sample : (Nat × Nat) := (0x48204888460220884860204305006231201402a14184c2215120940894580c10894088454834088c44814180d008a45805008141008804221804808864181c0882580c4029140a4140210805022140301c028340a094020402816010408840090410480c0640a150c024081400824804820104180d088541009080501809, 56)
def q34Witnesses := unpackWitnesses q34StockWords [99008, 362688, 626880, 893120, 1155216, 1411140]
def q34Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x204102081040820410208104082040fa47d03d0de80ee37513a81d40ea07503a81d02e807403a01d00e807403985cc0e606f23781ac8d606b03581ac0ce45c5a8ad3869634911f2cd144ed2510b3c06a001 0xe0f44ae61c1824b0b8c4060f44ac496161880c1e895692c2b3105524b0a8c405e01c2f19a173d11b18705a92c2b31036bd10b5870d292c29310163d10ad8705492c29310144941912594064dde320cf18d64cc404831420026af01047806a26008277a232b0e3852872492c26321ca18ac8cc40c23431a1958a0c7c486284cc388f31007802238c402e01f0e004469880340104af442462191b0e089259ba6439b31bc5988174686363371618f858c50864a040f4e1f7a20f313875258326411c31ac898806c6282a01e5a9280d3d115d89eacc38594a70ca50861259aa64e953210b8d0c58628aa04e150210a3d1231258a4f44136218930e1392869e9374b49628990c44c6e9862b10310078d0c3866e1a32b0c18f858c5125e8814c430961c23a50d2126e8a92cc4321c218df08c5702620081a1838cdc186570431f0518a22010c1006e8402b0300f81004c040100003f 13 5 13 6 2 6
def q34Data : (Nat → Nat × Nat) := fun i => decodeNode 6 19 0x3d12419a2cf444d8708bd10c61c1892c30c4064940b7a214c3825e883310c661c0c92c1a4a02bd3857a20ac4e15258298d4518a0af4411284224b041a1883141008423d10362184c3808c6e1188021a1843370865610c7c218a04c430587008d0c119b8232b04628080dc100f8201304010080fc0 i
def q34Tags := dagTraceTags q34Mask 56 (dagTagBases q34StockWords 0xea94d984834000146ff64760b060053abe30700d0a324001f81c1ad543f1401698451a888d082b0faebd 0xa914b54482800078255444608060851aaa28100a0a06400090101a1552e140132c4511008a082b0d2488 56) 9 q34Data
def q34States := dagTrace q34Mask q34StockWords 9 q34Data
def q34Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 4, 3, 2, 5, 7, 6] 0 i.val)
def q34Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 4, 3, 2, 5, 7, 6] 0 i.val)
def q34Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q34Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q34Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 4, 0, 2, 5, 7, 6] 0 i.val)
def q34Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 4, 0, 2, 5, 7, 6] 0 i.val)
def q34MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [17, 7]), q34Move0Map, q34Move0Inverse), ((moveSchedule qStages [1]), q34Move1Map, q34Move1Inverse), ((moveSchedule qStages [1, 17, 7]), q34Move2Map, q34Move2Inverse)]
def q34Moves := dagMoves q34MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q34Autos : DagMovesOK q34Mask q34Goal 256 q34Moves := dagMovesOfCheck (by decide +kernel)
def q34Check := dagCheckNode q34Mask q34Goal q34Chart (dagKnownCloses q34Goal q34Cuts) 49 q34States q34Moves q34Links q34Sample q34Tags
def q34RootAt (token : Nat) : Bool :=
  let s := rootState q34StockWords 9 token
  !dagAllowedRoot q34Witnesses s.2.1 || dagLocal q34Mask q34Goal q34Chart (dagKnownCloses q34Goal q34Cuts) s ||
  dagRef 49 q34States q34Moves q34Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q34RootBlock0 : treeBlock 0 64 q34RootAt = true := by decide +kernel
theorem q34Roots : dagCheckRoots q34Mask q34Goal q34Chart (dagKnownCloses q34Goal q34Cuts) q34Witnesses (dagRef 49 q34States q34Moves q34Links 0) q34StockWords 9 = true := q34RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q34Block0 : treeBlock 0 16 q34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q34Block16 : treeBlock 16 16 q34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q34Block32 : treeBlock 32 16 q34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q34Block48 : treeBlock 48 1 q34Check = true := by decide +kernel
theorem q34Verified : treeBlock 0 49 q34Check = true := (@treeBlock_merge 0 32 17 q34Check (@treeBlock_merge 0 16 16 q34Check q34Block0 q34Block16) (@treeBlock_merge 32 16 1 q34Check q34Block32 q34Block48))
theorem q34Blocks : treeBlock 0 49 q34Check = true := q34Verified
theorem q34Known : Known q34Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q26Stock) q25Stock) q20Stock) q10Stock) q18Stock) q27Stock) q17Stock) q9Stock) q3Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q34Stock : Lower q34Mask q34StockWords q34Goal 10 := by
  apply lowerDag _ _ _ _ q34Autos _ _ _ q34Known _ q34Roots q34Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q34StockWords; decide +kernel
  · decide +kernel
  · simp only [q34Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def q35Mask : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
abbrev q35Goal : Nat := qGoal &&& q35Mask
abbrev q35StockWords : List Nat := projectDAGStock q35Mask qBase [0, 2, 4, 5, 6, 7]
def q35Fact : (Nat × List Nat × Nat × Nat) := (q35Mask, q35StockWords, 9, q35Goal)
def q35Cuts : List (Nat × List Nat × Nat × Nat) := [q4Fact, q17Fact, q22Fact, q28Fact, q11Fact]
def q35Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[20, 33, 65, 80, 129, 132, 160, 20, 20, 20, 20, 20, 5, 17, 48, 100, 144, 192, 5, 5, 5, 5, 5, 5], rfl⟩
def q35Sample : (Nat × Nat) := (0x4820460a002a1120d02231120501028180e0181c06050603402291601404834088c44814603100a4502904603402894601440210805022141008100a0580410221002410814002212010500a0301046031028540a14020504825088544021080502214, 44)
def q35Witnesses := unpackWitnesses q35StockWords [99008, 362688, 630976, 901312, 1155216, 1427556]
def q35Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x1e3c78f1ab453a108781 0x5bd10c6298040481a20070fe88662097a2c7d10ac404043181f880242010003f 7 3 12 4 1 4
def q35Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0x34401c4f44262026201043103f10091008103f0 i
def q35Tags := dagTraceTags q35Mask 44 (dagTagBases q35StockWords 0xfb3082684001de8e196a004386180151414ff15821eb2805de080fb80126875b9c 0x9528825040009288190a0042c51400314d4d2140210b280568880f0201268250c9 44) 8 q35Data
def q35States := dagTrace q35Mask q35StockWords 8 q35Data
def q35Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 1, 6, 3, 4, 5, 2, 0] 0 i.val)
def q35Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 1, 6, 3, 4, 5, 2, 0] 0 i.val)
def q35MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [14, 21]), q35Move0Map, q35Move0Inverse)]
def q35Moves := dagMoves q35MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q35Autos : DagMovesOK q35Mask q35Goal 256 q35Moves := dagMovesOfCheck (by decide +kernel)
def q35Check := dagCheckNode q35Mask q35Goal q35Chart (dagKnownCloses q35Goal q35Cuts) 10 q35States q35Moves q35Links q35Sample q35Tags
def q35RootAt (token : Nat) : Bool :=
  let s := rootState q35StockWords 8 token
  !dagAllowedRoot q35Witnesses s.2.1 || dagLocal q35Mask q35Goal q35Chart (dagKnownCloses q35Goal q35Cuts) s ||
  dagRef 10 q35States q35Moves q35Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q35RootBlock0 : treeBlock 0 64 q35RootAt = true := by decide +kernel
theorem q35Roots : dagCheckRoots q35Mask q35Goal q35Chart (dagKnownCloses q35Goal q35Cuts) q35Witnesses (dagRef 10 q35States q35Moves q35Links 0) q35StockWords 8 = true := q35RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q35Block0 : treeBlock 0 10 q35Check = true := by decide +kernel
theorem q35Blocks : treeBlock 0 10 q35Check = true := q35Block0
theorem q35Known : Known q35Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q11Stock) q28Stock) q22Stock) q17Stock) q4Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q35Stock : Lower q35Mask q35StockWords q35Goal 9 := by
  apply lowerDag _ _ _ _ q35Autos _ _ _ q35Known _ q35Roots q35Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q35StockWords; decide +kernel
  · decide +kernel
  · simp only [q35Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def q36Mask : Nat := 0x555555555555555500000000000000005555555555555555
abbrev q36Goal : Nat := qGoal &&& q36Mask
abbrev q36StockWords : List Nat := projectDAGStock q36Mask qBase [1, 2, 3, 4, 5, 7]
def q36Fact : (Nat × List Nat × Nat × Nat) := (q36Mask, q36StockWords, 9, q36Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q36Stock : Lower q36Mask q36StockWords q36Goal 9 := dagShiftLower (width := 256) (moveSchedule qStages [1]) q30Stock (by decide +kernel)
def q37Mask : Nat := 0x55555555000000005555555500000000555555550000000055555555
abbrev q37Goal : Nat := qGoal &&& q37Mask
abbrev q37StockWords : List Nat := projectDAGStock q37Mask qBase [1, 2, 3, 4, 6, 7]
def q37Fact : (Nat × List Nat × Nat × Nat) := (q37Mask, q37StockWords, 9, q37Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q37Stock : Lower q37Mask q37StockWords q37Goal 9 := dagShiftLower (width := 256) (moveSchedule qStages [18, 10, 19]) q33Stock (by decide +kernel)
def q38Mask : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
abbrev q38Goal : Nat := qGoal &&& q38Mask
abbrev q38StockWords : List Nat := projectDAGStock q38Mask qBase [0, 3, 4, 5, 6, 7]
def q38Fact : (Nat × List Nat × Nat × Nat) := (q38Mask, q38StockWords, 10, q38Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q38Stock : Lower q38Mask q38StockWords q38Goal 10 := dagShiftLower (width := 256) (moveSchedule qStages [2, 26, 21, 13]) q31Stock (by decide +kernel)
def q39Mask : Nat := 0x1111111111111111111111111111111111111111111111111111111111111111
abbrev q39Goal : Nat := qGoal &&& q39Mask
abbrev q39StockWords : List Nat := projectDAGStock q39Mask qBase [2, 3, 4, 5, 6, 7]
def q39Fact : (Nat × List Nat × Nat × Nat) := (q39Mask, q39StockWords, 9, q39Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q39Stock : Lower q39Mask q39StockWords q39Goal 9 := dagShiftLower (width := 256) (moveSchedule qStages [1, 9]) q35Stock (by decide +kernel)
def q40Mask : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
abbrev q40Goal : Nat := qGoal &&& q40Mask
abbrev q40StockWords : List Nat := projectDAGStock q40Mask qBase [0, 1, 2, 3, 4, 5, 7]
def q40Fact : (Nat × List Nat × Nat × Nat) := (q40Mask, q40StockWords, 12, q40Goal)
def q40Cuts : List (Nat × List Nat × Nat × Nat) := [q12Fact, q14Fact, q13Fact, q30Fact, q32Fact, q36Fact, q19Fact, q31Fact, q5Fact, q20Fact, q7Fact]
def q40Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 18, 20, 33, 34, 40, 129, 130, 132, 136, 160, 9, 7, 14, 17, 24, 36, 48, 144, 7, 7, 7, 7, 7], rfl⟩
def q40Sample : (Nat × Nat) := (0x382500211020500091002400a00c261209806230148a0c0e01422180e0182c120b0142a182c120b01229060a00c2200a8501a0c06824824406230188860311209500a010280488408a442281120d02231120510088042201482040a0221905068220902210603402894601440210301c028340a094020808140c068060b01824482612089008100a0404820088404220c06406130c024041200824402810084180d08854180908050140b0884c1009080481409, 80)
def q40Witnesses := unpackWitnesses q40StockWords [74384, 337040, 600208, 864400, 1075236, 1400976, 1663024]
def q40Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x7240e481c9039207240e481c9039207240e481c9039207240e481c9039207240e481c9039207240e481c9039207240e481c9039207240e481c9039207240e481c9039207240e481c9039207240e481c9039207240e481c9039207240e481c9039207240e481c9039207240e481c9039207202e401c8039007200e401c8038e171c0e381c7038e071c0e305c6038c07180e285c40b88070c2e181c3038607082e101c2038407061e007bf877e0efa1df03bc8f7906f20de41bc837906f20de41bc077806f00de01bb877706ec1dd43ba07730ee60dcc1b9837306e41dc81b903710edc3db81b6876d06da0db41b6076c06d42da43b4076806d00da01b4036806ce1d9c1b3836706ce0d983b3036416c42d7c7af075c16b61d683ac87580eb00d5c3ab07550ea81d4c3a9834a4e940d243a407451e843d081a1034206840d081a1034206840d081a1034206840d081a1034016800d001a0034006800d0019f0b3e067c0cf819f033e067c0cf439e833a1e721ce039b873516681ccc395a32a0e502c9c3920f2406461c883900b1f0e364c6c189271206202c401880310061c2c305850b0a06140c243830f0606082c10182030216040c0058002fd1dfa0bec57d82fb05f41be817d02fa05f40be437c82f80df00be017c02f70dec1bcc77982f115e20bb87760aea15c67b70f6d0ace658a9b1416092bd25705accb580ea93d3eaa60f491a8b3d0879e953a1a6e34d0698112aae4d448e68fd11f8235545c78b43139a251432c854905aa024bf0a7e00fb09ed4bd057794ee85d25b9867284e029bf0b62e6a50cfa9955316a62c0c5058052df15ac8b1a15a4aaa55486a521414a7284e40982530024e9480e8a3108620463ece7924ec31cc637ce6c1ccf498e82fd05ba0ab6142a232a41287660d8a18562a3440a059406e2082c0178001 0x16361c67a92ccf24a09e24b33b7a2276620ce52589c8c533849627031458de899d24b33792826e92c589280b13161616262b0034581898afb131571a62ac34c585280b019015f1a02a6034548680a700a14d19a29833452c668af00d15d4a62baf585718b0ac81615b62c2ae358571280ad8d01551ac2a834c54c080a90d315a1a628e028d45280a300a34f4a029004c514050a20cd3514a6286028508668a080a14019a2acf58564c80aabd61547a62b063454d280abc941567a22aac39551870a924b151326a9064153cc6b9a9881534a02a4c4c5458b0a519015031a2a2f4c4fccb0a81933484a0290040d3d298a781314d4ac29e940d18cb1a299014c4a629c64052d298a7b1314a32629294c539281a6c9414d7a268cc4d519882a630e14b496294636524c40a2253146326286640509298a425334332c28a64c504c68a025014862627e6344f9280a3bd51467a6686c58515898a24943437a7684f4450d89ca130e1414a728092c4fcc9c9f18813c928268f444f5e889d24b1394962666204e12589918813b92c26f2504c5e889e01253b7a2260c384ede8897b0e13792825cf444e98809ca5013832026f2504b5e889aa5013602a26a94c4d5898983d613192825cf444d007a99a501323202632504bde9c96bd11307a225ec384ba4a096bd11199285e2f59a31e887899648c3106580424b003c924945209285e0f4fa2de8878193cbe321916620cac06c95804923aae243250475eb48c3d130762cdcac4da29870838d64e51a6914314ca806c95004923aae24525045de89773166e4626d12c383b86b2720d348918a22c92ca18c405d807c8600422a92ca14c405d007c850042532504518705e25368849617202a4a1e8a93bd111349624c643a1cc409155911c93224a00c44a4a1703d66847a21c0659210c4092012523006a4355c48a4a08dbd39117a25bec59c1189b41b0e0df1aca0834d20c6288d496110928602f59a09e888099648231024200e43e4a140bd10b83219026204800928f803d0e9285fef59a01e887f99648031063c04247803c8e3d151a7a25bcc439fd8706f0d0cb619b8fe314476ab88db0e2dd4acdfa941b6d26b3f24b0dd02c9fa04136c06a3f00211c928236f4eb698833eb0e0da1a08fa314469e897e310e7c61c1f83432d466e3e0c511792ca21250be9eb33dbd10fa32c8f662044a4a287c942d97a7cf4f44364c9e5a190c7a31023204b462ab88bc941117a25b0c59be589b6b31067961c1b03593e469a6b0d047918a628c41c4d8813c30e1164a022a640450682898d007818a22555c4464b56abd36777a21aa64d1dcc408849450f9285f0f4f9d9e887c193cb33218ec620438096834965029281fcf5a3ede887b31667561c19834e28866c8681390c01b1dd2594064a07d3d10b162cce8c3832c69c508cd90b7aa2172644164b08525010932021034031c0987eb130c602020f55c41a4a082bd29047a21f2c38b4d2b2582536d24a0ce692c314084620100a00151bf2644124b0618d310303020555c4064a07e3d38f87a215ec593d589b3930e09f19b2000553fc0927f4940dd6269fac413f1870572534f74a0ce292c30806c4f00a8fbaae1f5250361eb27cbd34f87a215ac593d189b3830e0c11a113a3363dd8984d00a2f6aae1ed250b4deb269bd34f57a21e8c38b01284600108990141dd5643924c86f3d90cb1b21e60543a2ab8704940d97a2158c5934589b37b0e09819b1e40553c40927800f4ec92a1df55c3ba4a06fbd10dd6271b0c382ad2b276a558d34a69a09419b92584b80a8ecab21c6f643ad298751930e91a619406438a4cc648d98e8aae1c325a371eb46bbd10cf626cdac383206b44b0cd8e702d1cc0363140b072d570e49281c6f49389e8a70bd10db6271acc38b412b2692534a94a0cd892c31809c620130950151c155c37e4b46d3d68d57a2150c4d9ad870618d689419b1bd250375e9c6e3d10db6271b4c3829d2826724d66a49618404e24c0546cd570d892d1af250359eb46abd10a662699ac419a5870608d689219b1572643524c069c962d07b21a4f58a712995fa5009103218005823c0504700a0d1aae5a125ab3e4a0683d68cf7a219cc5a3358715fa568bf02d11a028332ab865c940ca7a4992f45321e8863b158c662718ac4d31189861b0e0c24a718292c244cb26019349c32097e6359a0c405b4990b17b2542c642846c85c5570b4928158f5a295e894c3168981ad17c0492f407a55b190b062c152c4ca5d2c9502562954a612e0642800b04a8130bc62657294c2ecc985d0d30b9026150f58a518b04a0d60b8aae16b25a2ce4a057bd68a47a253ec5a27c6b45b80f4b692816af442b989c53b108a361c53c94ea4d2844f01389302116955c2ce4a056bd68a67a753ac5aa4989c4e8d68921a716555c2c64a055bd64b07a695ef442b989c56b0e2914a11220422b2ab855c968aa928152f5a2a1e8853b168a661c53895a2700b452d570a4928146f5aa6d8b54831389b1ad12034e28aab850c940977ac940f4d27de884f31389d61c13894226d2584d19389932651e642262ab84bc9689692812af5a251e8849b1689261c12295a2412584799688e32111a6402264b24149407f7ac0f6f441d18b233b0e0849289032501e9e8837b13c6661c11804b22c07a45557089928106f441f989c3cb0e06e4ac8e694d1b128232a4b07861c11094121d2803224b08632010a340212ab841c9687d7ad0eef441ad89a31b0e0829289032501f1e9c3b3d10726278c4c382000963fbd107e6218fac391f187038a50c6a49b8c292c1ee4a23d4940797a78f0f4b1dde8a3b3d10706278d2c431818703ad570749280dcf591cde9a393d10716270e0c381a128437d5706e92d0db2501b1eb435bd106a62d0d2c381a12b433c944669280caf4f191e9631bd14627a20c2c4e1818702dc964559288a525013deb025bd124362cc6ec4f85d870218d64371a784c33705c6282a494451928094f448d989f0b30e0361a784a3370586282f812c5e01e8bb55d172ab82dc940537a209cc4e1258712d256e344acc8094f8fd29b18250e2f4a0c2a92c1680b61a01644002787e04d0c00861781042401582a0081218712ba506564a042892c164c802c0d00570208ac04008c0560a002055aae8a955c14e4b426bd68477a247cc5b8b989b09b0e03e1ad85c34d08866e098c50529288a3250131e9c233d123d627c24c380f469e108cdc1218a0a004b13de8827310c4d61c898c388f128716a4de114960780430b406e1000ac1100409725112a4a024bd3c487a588ef45119e891db13e2c621c20c380ec69e160d0c1f19b820314116aba22557043928084f5b0d1eb220bd5c407a787ef4d0f9e8a1ebd103c627076c380e92b60ea564394a787094d8ad28707a4b02702103202a0deaba1b55703592d86925a0ce4ae19494431928060f5b0bdeb4173d102d62d058c380ad2b615253c1b4a68529430a12830724b02702d03002a09aaba12d5702492d84725708a4a210c940207ad03ef440798b60eb1681c627836c4e0698710ca56a184a703205a06009c0bc9441692802af4f051e9609bd14127a2022c4e04187007a53c0e4a181a92c0324a205c9400a7a7812f4b021e8a03bd100662700ac3881129f01a50e0149600804f00c0860100ac0100400007f 15 5 13 9 1 6
def q40Data : (Nat → Nat × Nat) := fun i => decodeNode 9 22 0x7a24518b10b4a0418c81061a0418068f07ac3b1280e41a0390698d532032cc68c8928315e88c561cb15870c54a030d898c27a6300c98c06262752809b7a22698709a496268c6c9a310269898927aa241e98906262424a08e6272398708e4a72392588e327238c408e7a2220092827a21f5880794a01e4c80799281dc0a86f6261a407a674a0194c806592818de886261c18a4a0617a218403c600091780245d928161e8a577a215cc8657006158092550069564a05400714c0925200794803c51aae13e4a04e7a7139e884d02592eab84a92812928049320124682491a0126ab84892d1224a24792811c0964702711406c459321092804232010868042aae1024a0407a51024b03f0300feab83e9280f80aa3e0248fa4a03d6208f58703daae0f24a03c7a68f1e883c6260ea4a0397a20e58703902a0e00aa370248dc07a37aae0d64a0354ab0d6ac8344a60d0c98341a60d2ab83202d0c806c32aae0c24a0307a48c1e8a307a20c2ab82f92d0be4a02e7a70b9e882e6270b98702eaae0b64b42d9280b5eb42d7a20b64c02c92c0b1eb02caae0a5eb4297a20a58b42961c0a6ab8289280a1e92287a28a1e882862b0a189c286268a18982861c0a129c284960a0c9a2831a8a00922601e8998982432609069824026092ab82201e88a4a0217a2086ab820928082ab81e928079e9a1e7a207989c1e61c07aab81c92d0724a01c7ad071e881c62d0718701caae06e4a01b7ad06eab81a928069e9a1a7a206989c1a61c0692841a496068c9c1a32606aab81992d0664a0197ad065e881962d065870194ad0652581932d064c84193200640961701e85eab816928059282154a0054c80151a0056ab81492d0524a21392804c096137a20498861261c849870129288464a0117a7845e96117a2845e8811aae0424a0107a6841e881062704187010aae03e4b40f92803deb40f7a203d8b40f61c03d2b40f92883a4a00e7a7839e960e7a2839e880e6270398700e02583007a0caae82eab80b92802c0b60b3200286800a0208280800aaae826ab80992d0264a208928020096087a201d8860761c81d8700792881a4a0067a7819e96067a2819e8806aae816ab805928015eb6057ab815e9e057a6815e8a057a201589c0561c0152b6054a781529a05aae812ab80492d8124b40492b8124a204928011eb6047ad011e880462d011870044ad81129e044a18112820402d012aba03aae00e4b60392b80e4a20392800deb4037a200d8b60362d00d89e0362700d8700302d00c09c0392880a4a0027a7809e96027a2809e8802627009870024a78092860249600a4a201928005e9e017a5805e8a017a200589c0161c00409e01021804056010040040fe00 i
def q40Tags := dagTraceTags q40Mask 80 (dagTagBases q40StockWords 0x27c0ff87c708881c0000443ff07e3086006306000328c090b8654600d0aa9bef080006f07380ad5500862409280fe44001a00051036001200b65501af80006d8d052319aebdd 0x51004084040088100000280ab01b2805006006000328d890d0554200a0aa02f5080003a04200a15580862409280a346001408051036001200185501180000760d052318a4888 80) 11 q40Data
def q40States := dagTrace q40Mask q40StockWords 11 q40Data
def q40Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q40Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q40MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [1]), q40Move0Map, q40Move0Inverse)]
def q40Moves := dagMoves q40MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Autos : DagMovesOK q40Mask q40Goal 256 q40Moves := dagMovesOfCheck (by decide +kernel)
def q40Check := dagCheckNode q40Mask q40Goal q40Chart (dagKnownCloses q40Goal q40Cuts) 356 q40States q40Moves q40Links q40Sample q40Tags
def q40RootAt (token : Nat) : Bool :=
  let s := rootState q40StockWords 11 token
  !dagAllowedRoot q40Witnesses s.2.1 || dagLocal q40Mask q40Goal q40Chart (dagKnownCloses q40Goal q40Cuts) s ||
  dagRef 356 q40States q40Moves q40Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40RootBlock0 : treeBlock 0 64 q40RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40RootBlock64 : treeBlock 64 64 q40RootAt = true := by decide +kernel
theorem q40RootVerified : treeBlock 0 128 q40RootAt = true := (@treeBlock_merge 0 64 64 q40RootAt q40RootBlock0 q40RootBlock64)
theorem q40Roots : dagCheckRoots q40Mask q40Goal q40Chart (dagKnownCloses q40Goal q40Cuts) q40Witnesses (dagRef 356 q40States q40Moves q40Links 0) q40StockWords 11 = true := q40RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block0 : treeBlock 0 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block8 : treeBlock 8 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block16 : treeBlock 16 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block24 : treeBlock 24 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block32 : treeBlock 32 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block40 : treeBlock 40 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block48 : treeBlock 48 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block56 : treeBlock 56 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block64 : treeBlock 64 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block72 : treeBlock 72 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block80 : treeBlock 80 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block88 : treeBlock 88 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block96 : treeBlock 96 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block104 : treeBlock 104 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block112 : treeBlock 112 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block120 : treeBlock 120 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block128 : treeBlock 128 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block136 : treeBlock 136 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block144 : treeBlock 144 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block152 : treeBlock 152 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block160 : treeBlock 160 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block168 : treeBlock 168 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block176 : treeBlock 176 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block184 : treeBlock 184 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block192 : treeBlock 192 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block200 : treeBlock 200 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block208 : treeBlock 208 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block216 : treeBlock 216 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block224 : treeBlock 224 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block232 : treeBlock 232 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block240 : treeBlock 240 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block248 : treeBlock 248 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block256 : treeBlock 256 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block264 : treeBlock 264 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block272 : treeBlock 272 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block280 : treeBlock 280 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block288 : treeBlock 288 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block296 : treeBlock 296 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block304 : treeBlock 304 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block312 : treeBlock 312 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block320 : treeBlock 320 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block328 : treeBlock 328 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block336 : treeBlock 336 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block344 : treeBlock 344 8 q40Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Block352 : treeBlock 352 4 q40Check = true := by decide +kernel
theorem q40Verified : treeBlock 0 356 q40Check = true := (@treeBlock_merge 0 184 172 q40Check (@treeBlock_merge 0 96 88 q40Check (@treeBlock_merge 0 48 48 q40Check (@treeBlock_merge 0 24 24 q40Check (@treeBlock_merge 0 16 8 q40Check (@treeBlock_merge 0 8 8 q40Check q40Block0 q40Block8) q40Block16) (@treeBlock_merge 24 16 8 q40Check (@treeBlock_merge 24 8 8 q40Check q40Block24 q40Block32) q40Block40)) (@treeBlock_merge 48 24 24 q40Check (@treeBlock_merge 48 16 8 q40Check (@treeBlock_merge 48 8 8 q40Check q40Block48 q40Block56) q40Block64) (@treeBlock_merge 72 16 8 q40Check (@treeBlock_merge 72 8 8 q40Check q40Block72 q40Block80) q40Block88))) (@treeBlock_merge 96 48 40 q40Check (@treeBlock_merge 96 24 24 q40Check (@treeBlock_merge 96 16 8 q40Check (@treeBlock_merge 96 8 8 q40Check q40Block96 q40Block104) q40Block112) (@treeBlock_merge 120 16 8 q40Check (@treeBlock_merge 120 8 8 q40Check q40Block120 q40Block128) q40Block136)) (@treeBlock_merge 144 24 16 q40Check (@treeBlock_merge 144 16 8 q40Check (@treeBlock_merge 144 8 8 q40Check q40Block144 q40Block152) q40Block160) (@treeBlock_merge 168 8 8 q40Check q40Block168 q40Block176)))) (@treeBlock_merge 184 88 84 q40Check (@treeBlock_merge 184 48 40 q40Check (@treeBlock_merge 184 24 24 q40Check (@treeBlock_merge 184 16 8 q40Check (@treeBlock_merge 184 8 8 q40Check q40Block184 q40Block192) q40Block200) (@treeBlock_merge 208 16 8 q40Check (@treeBlock_merge 208 8 8 q40Check q40Block208 q40Block216) q40Block224)) (@treeBlock_merge 232 24 16 q40Check (@treeBlock_merge 232 16 8 q40Check (@treeBlock_merge 232 8 8 q40Check q40Block232 q40Block240) q40Block248) (@treeBlock_merge 256 8 8 q40Check q40Block256 q40Block264))) (@treeBlock_merge 272 48 36 q40Check (@treeBlock_merge 272 24 24 q40Check (@treeBlock_merge 272 16 8 q40Check (@treeBlock_merge 272 8 8 q40Check q40Block272 q40Block280) q40Block288) (@treeBlock_merge 296 16 8 q40Check (@treeBlock_merge 296 8 8 q40Check q40Block296 q40Block304) q40Block312)) (@treeBlock_merge 320 24 12 q40Check (@treeBlock_merge 320 16 8 q40Check (@treeBlock_merge 320 8 8 q40Check q40Block320 q40Block328) q40Block336) (@treeBlock_merge 344 8 4 q40Check q40Block344 q40Block352)))))
theorem q40Blocks : treeBlock 0 356 q40Check = true := q40Verified
theorem q40Known : Known q40Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q7Stock) q20Stock) q5Stock) q31Stock) q19Stock) q36Stock) q32Stock) q30Stock) q13Stock) q14Stock) q12Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q40Stock : Lower q40Mask q40StockWords q40Goal 12 := by
  apply lowerDag _ _ _ _ q40Autos _ _ _ q40Known _ q40Roots q40Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q40StockWords; decide +kernel
  · decide +kernel
  · simp only [q40Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def q41Mask : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
abbrev q41Goal : Nat := qGoal &&& q41Mask
abbrev q41StockWords : List Nat := projectDAGStock q41Mask qBase [0, 1, 2, 3, 4, 6, 7]
def q41Fact : (Nat × List Nat × Nat × Nat) := (q41Mask, q41StockWords, 12, q41Goal)
def q41Cuts : List (Nat × List Nat × Nat × Nat) := [q15Fact, q3Fact, q34Fact, q10Fact, q2Fact, q19Fact, q33Fact, q37Fact, q9Fact, q25Fact]
def q41Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 18, 20, 65, 66, 72, 80, 129, 130, 132, 136, 9, 7, 14, 17, 24, 68, 144, 192, 7, 7, 7, 7, 7], rfl⟩
def q41Sample : (Nat × Nat) := (0x1800903218308848220800905209209200140068203a082250602041c82050480612222102281602112084089058088070480c420c050221406230148a6032014420512920980383c884c0c2603058061300c4622150181c482500c12030580a8501a0c22510190d80c1019080a154824488450703d20d022311205060340229160140805008140881440220108860120104808864141a088240884603100a450290500840c0700a0d02825008202050301a0182c06092211888424020402816010404820090404420c06406130c024041200824804820104180d08854180908050140b0884c1009080481409, 105)
def q41Witnesses := unpackWitnesses q41StockWords [99008, 361664, 624832, 889024, 1155264, 1417360, 1673284]
def q41Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x908090809080908090809080908090048fe18f838f618f608f038f008ee18ee08ee08ee08ec18e638e418e408e408e408e408e408e408e408e408e408e408e408e408e408e408e408e408de38de08de08dc18dc08da18da08d818d618d608d418d218d208d208d208d208d208d208d208d208d208d208d208d208d208d208ce28cc18cc08cc08cc08cc08c258bc38aa98a628a608a228966890388c287e78783878087428740872186e2860785e185e08564850385008500850085008500850084c284c084c084c084828480848084808480848084048400840083e183c183a18381838083808380836183418321832083208320832083208320832083208320832083208320832083208320830182e182c182a1828182618260826082418240824082408240824082408240824082408240824082408240824082408240824082408240824082408240824082408240824082408240824082408240824082408240824082408240824082408240820281e181c18144812180e280c180828080806180417fe37fe07ee87ec17ec07ec07ec07ec07ec07ec07ec07e827e807e617e417e407e407e407e407e407de37d647ce47ce07ca27ca07c247ba47b247b207b207b207b207ae27ae07ae07a837a807a807a807a807a807a617a607a607a607a607a607a607a607a607a607a607a607a607a607a227a207a2079c379c079c079637960790379007900790079007900790079007900790079007900790079007900790078c278c078c07882788078807842784076eb76a276627641758674a773a8734372e371aa7162704970026fa36fa06f436e486cad6b896ac66a066908680866e965c96506650064a364626403630861ca61065fe95f265ee25ea25e625e225de25da25d625ce45ca25c625ba65b435b405a0a59c258e758e058e05807580057085665554955405429542052ea52e051aa50e650c150a15062506050604f2a4e854e804e614d2a4d204d204c664b494b024ac24aa14a6249e449c1498249424940490248e148c148064746460a45a344894461446043a643a0426a41e441e04107410040e14064406040603fc53f063dab3d053d003cc23cc03cc03ca13c813c613c413c213c013be13ac9398a38c6376b364934eb33aa32a8314b30a52f6a2dec2c6c2b872aa729e62907276d243a22cb20d01eef1c361a301830163014cb134c11eb0fb20c1d09b306d7052d031100370001 0xedd880dca501b832036e3406e5898dcbd13b43103680086e1898dc3d13b33103660086dd898db3101b77a236c92ced4c40db3101b549a3686346cc668daa501b56203689406d1880d9a501b362072a92c654010d93d21b292c756c406c5280d79901ab1a07549346b8668d500d1b2928758935e99269ca24b1b031a35a3346b006ad300d194004726c3864c629c724b18e18a3632506c1281d199078d310346041634010d831038c310318008e2d258c58c51af92835c94e6b5281d119078a310344041628010d6b103893103120086b1898d08131ac7a6350f44e49258d5c941a9620b4ec386a929cd32503a4320f226206a5e98d44941a77a734ac4ee41258d33101a549671e620e224a0c424b3807a230092c691268d198d1a219a342034691e98d1bd31a27a6342f4c67c668cf0cd1a001a33a028670050cd8cd19a014332334660668cb0ca39d32c73864067d298cf25339d626b3ac4167d870cf24b19b4a633a64c668c80cca5339a32c33864c661280cba5019d7a6734c58671898cdc9439a7a7732f4466989cccb0e19849632e620658628cb19018892830cf44654050ca30f19262031c94062cc80ca3d319149a31a634628668ca3d318f49a318634624668c9c94185496325250645e9cc830e18f4a731d250635e9cc6253984310317250629e9cc4a53983310311250609e88c44941817a2300c3861c0a8c34941827a230d250605e88bfb0e18562c30893460cc68c14941817a22fcc38601e88bfb0e1807a22fcc385fde88bf30e1797acae8f49571e89aa31673e626ddec385506b29f0d34ef18a6fa0365f4024be31517361e2f8f645e1eb0bbb1357592cab7250cf1eb3773d113c32c9dc620569e899db16752626ddac384ec6b2a90d34ed18a2bd2515664a194bd3eec7a225264f46cc867618817b1a5af755cbade88759882ea61c1d43145e8050bcd5717862b2e4c3cddd2b79d2506e94962ee05b4e80828c80ace90045d0c383a0628bb5571759282baf44ca18b3923106e761c250359490682738c52e64961cc0085daab972b0e0e518a2eb55cb91870720c5369620ecac40b8d870b7a5016c3202d2341594680718c5174aae2e6f5a5c9e99a7a5376849aec8934b89258b718d16b19a29e04d5a006ab200d0e20042e4f4cd9926bb024d2e14962da6345a8668b300d56001a1c2008d392b3a6a536e049629c05953409a700021719286e094fb7d258b8013d180159be0085be4a0b73d396d4a769664fb70c40a5813d1600f9b80085b24a0b5bd396a4a769464fb6cc40a5013d1500f9b60085a6ab8b449694e7ad2cef445998b48ba506de49629205a450054b2c941647a72c6c4f589872b0b0e1604a769864f57cc6f6e98815eaae2bb25ac8de9b6d3d11233269b462057aab96cbd10d93105b0c38360628aed572d761c1ae31456e4a2acc943387a7dacf444e0c9e89990cd63102b034b572ab8ad3d133762ce8ec4dcd58836ab0e1371aca8e34d4d46826a8c515baae2b525acd1e9b6a3d11343269a86205664a1a33d3ed37a25e6c43555870a3193d123219e663734cc40ac5572d27a21a462055c0b5ab01095600f56c92c2d80115ab0e0b518a566c382cc6295924b0b2004562c382c46295830e0b018a55c6202b8010aabd12a761c20a63729cc415324b0a618a54ac38294c40aabd132c621d48c384b0c868218dca43102a72595464a0a43d1154aae2a7250549e88a7b0f54761c66695944529b992506d149620402a4ee4c8a9496151aae28cf444418b2a2b136d061c2023365400aaa7c9614e63229ac58531268a598d14a19a292034522ab89bbd65477a6a8cf4443d8b2a23136cf61c200336ccdeb299bd35457a2288c383fc050a0d5713c928250f594e1e8887316531626d9cc384806847f0cd943aae276f444dd87086a565424ab26694d4c128366a4b0fd01528355c4f64b49b3d112f626d98c384b52588f8d08fc19b28005a4fc06c9f55713d7a2274c4d4d5871982565324a6a16941b2d2588f00d8fb01527955c4ee4b49a3d110a626d94c383e866c9d3d6139624272f584740809c55713792d26d2504d5eb49a3d1109626a5cc41b258709624b0f919b21b2644ce4b1983d91327ac1ee0283d805098d5733092d65f2504c1eb497bd112e61c6389364acc408e00d8f501425b2504b187081a5352b4a0d4692c3d065494d5712892d24f250491eb491bd1108626a42c41b21870900d692a7b023c04c4a6ab963b0e2c649625155cb1525893d572c461c24c05a49406d61a4b124aae58492c48eab960b0e1227aa23804c486ab95124b120aae23f250479eb48ea5291c320d8062046eab889c9410e7ad210f4ebf98b47f0d69197aca1ac644458b085b132fd4b2604958bed2987e81910202c1f604c429eb17d3160fa1ac23755c44a4a0883d69077a2602c5a3c928282a4b1011ad23403d4664b28c3d9117620628940458c808a8d011402022755c44a4a087bd69097a720cf44c018b57cb1390449620035a3e469c86bd65117a6a20f4443d8708755710d92d21925042deb4853d110961c206620422ab883c941067a25f0c4e3e069c82c941047a2206c4ebd129c7a0d38fd7aca04f4d405e888030e0ff3265ee6423faab87ec968fc9281f6f5a3e9e887cb0e0f84961ee65a3d8c847a9900f418a1e7250ab5e88793108f161c1e09423ce4a1563d12ab49655492c3ca4a078c942a84961e1250aa5258774944ec9281cef4f38de966d3d14d67a219cc4f3218865fb0e0efaae1daf443998b274b134e261e9aac383352b268a534cb4a097c92c3baab876c968e47a69a8f4432989a5eb0e0ec9281d0f4f365e8a69bd10d062798ec432f187059a50cad49b94e92c3ac07e755570e67ac9d2f4d3a1e8870b0f8d861c18c95930d26a5da4b0e7aae1cd25a3964a0723d10d761c18a94d30926a5d24b0b232696c641298c4071d570e292d1c2f5a3818b46fb160de49a9ba9342e52586e18d0db19a1b555c3664a06c3d68d77a7182c412e1870582504a54961ad250355e9e6a3d14d37a219ec4f3258865bb0e0b54a19589372912586900fccd7ac9a2f4d341e88633164cf61c19d55c3364b4664940cb7ad194f4431589a64b0e0c049b15664d28cc40645570c792818cf5a315e9c623d10c362d184c4e305870602538aa320952629288c405fc940be7a797af452f1e885db13cba621972c3f2e18725bb0e0b44a195e937285258593134b662096ac382ad29a5a24b0ae31b15062a2ce4a0593d38b17a2160c382a928257a4b0ae32715b2502b1e8855b138aa6211529422a0c9c53bd10a662194ac3929187051a50ca249b94292c26e4a24cc940947a791ef4b219e8a40bd1266627ca2c4388d870330d3c511a188633708c6285055749faae134f442798b649b1649d62b92cc4d2458864730f48561c900c38a712b73225666f4a6cc29439812832824de2249613805b1900b2378134610218c004114006e2100ac2200413755c26a4b4483d347f7a24dcc5b97d89b10b0e06e1ad8be34d10466e108c509992812af4f211e8a3f3d126d627c9ec438818703d250e2f49b8ea92c1b469e278d0c4019b85e32b0806284c00fc97aae126f59259e9a4abd108d61f106c389392b32f250e4b49ac3e92c1380b22f010c4b01a87e02b07c0104a55709392d125250245eb6483d108261c4d695b93529b2da50e4a49ac3c92c1e4c9a3e19062e3158e86201ac0b62681345b0218940350f805617007c1e00411f55c23a4b446bd688c62d116c589a92b74424d68749a43a92c228c68448cd06a02d91003521c0681e80ac1d00410d55c2164b6424940837ad104f4e9a58b72d313e49620c38c381dd28239a4b0691ad8b434f1246821e0cdc1c18a103250201e9e3fbd147e7a24d0c4f9658870db0e07b4a1c5a9371c9258340d3c591a18763370b46560d8c507d01f8f2c4d1f18823db0e22a4a6c2c92c1d8c6d1318a82a02686802b09803a0b00207a9280f2f4e1e1e883bb0e2534a7c529418552583b1938530278520410cc0560a8020757a20e8c431cd8723930e2524a1c8a93784d258290d0c4519b86432b04c62838d570707ad8c8f591bde9a373d146d7a20d8c5b1398b235b10c6a61f8d2c391a18701d2564674a6cb094392126f0d24b0310150cd55c1964b6324968639288c5250185eb6303d685f7a20bcc5b17589e26b1345c6258b6c431698722cb0e0584ad8ae94f0e129a2b250c554a0c8e9378652582a193c2a3268a66378b0c562918804401b06002a146ab828496c4f92809cf5a135e9c263d104b62d094c4e12587024256c474a786c94111926b0c24b029320c5662b114c402201382400f08755c10a4b620c9444092807ef5b0f9e9e1ebd2c3c7a2876f440e98b41cb13c3862706ec430d98841ab0e2314ad46094e0d0c9e19990c2831a8646200c40b41801382f92805cf4f0b5e8816313c2b621c28c380a929c14a5082849b04e92c098c9c1298d824021047250089e9e10bd14207a203ec4f0798860eb0fc1c61c836c3806929e0ca50c1849b82e92c058c860a98dc1431582662004a4a008bd3c107a281ef4403989e06b10c0c61f816c3902987103253e054a1c0893780525804990c0831bc0462b01cc4003013c0502180803700c05601007c0100400007f 16 5 13 9 1 6
def q41Data : (Nat → Nat × Nat) := fun i => decodeNode 9 22 0x7a26c5e89ae7a269d881a66206418818d62062a4a1739285bd8816e9285b129d6c6205ade996792859529d657a65924a1627a758988161496585e994d7a6531e994b7a65280694461c401259007a63e1898f89283d989cf661c3d9258f63103d8c80f50143ade98e29283824a0de7a7379870de4a737a4a0dd7a737529cdd928371e9cdc4a73724a0d402a33a4a0bd62c2e9268ba31a2ea4a0b87a22e1e88a57a2289870a2009281ec89eaae26405098aae25d8ac9702da5eab893aae246ab88f7ad23de988e92823009e8c92822de9c8b4a722e4a08a7a722929c8aaae2264b4897a22258b489928221e9c88627a218728861c22129c8831ba22ab885aae20eab881aae2024b4809281feab87e02d1f803c7e7a21ceab8709281c24b06faae1b80aa6e92c1ad8c86b62c1ad2686b31a1ac6686b01a1aeab8697a69a5e88697a21a187068aae1952ac65aae18c0b46301b18eab8617a2186ab86092d181eb05f7ac176ab85a92d16a4a05a7ad169e885a92c165eb059aae159eb4567a21598705692814d870534a094dec051aae142ab84eaae1340b44d01b136ab84baae129ea848aae11eab845928115eb4454a5114c8245aae10407a4192c901ec83e6200f8c803e1a00f80803eaae0f24a03c7a68ede883b61c0eeab83992d0e64a0397ad0e5e883961c0e6ab8379280d9e88369280cde88336270cde9a327a20c9870323260caab83192d0c64a0317ad0c5e883161c0c52583132d0c4c84313200c4628319280ba4a0299280a24a026aae08eab82292d08a4a02101f886ab8207a6881e8820aae07e4b41f92807de881faae07a4b41e7ad0798b41e62c07926a1e49a078c681e19a07aab81d928075eb41d7a70764a01c7a7871e8a1c7a207007e1c7a686de881b61c06eab81a92d06a4a01a7ad069e881a61c06aab819928065eb4197a7065e881962d06589c1961c06529c19928061e9e187a2861e88186278618861861f8618721861c0618821761c05d25817928059e9c167a205987016496058c9c16928055e8815627055884154a1054c9c157a20518861461c851870144a185126e14496052aba12aae0498b61262b8480b612aae0464b41192804007e10aae03de9a0f7a203eab80e92d03a4a00e7ad839e880eaae0364b40d7ad0358b40d62c034c680d19a03406a0d01a036ab80c92d8324a00c7ad031e9c0c92802de9e0b7a282de880b01f82d8820a61c02a4a0097a7025e880961c024c9c097a20218860861c82187008aae01deb6077a681de8a077a201d8b60762181d87e0761c81d870074a681eab80692d81a4b40692881a4a0067ad819eb4067a20198b606627819896066218198720661c0192b6064a7819286064a0818c9e0631b818c4006aae0164b605928015eb4057a7015e880562d01589c0561c0152b6054a781526a0531001409c05aae0124b6049288124a0047ad811e9e047a5811e8a047a20118b40462781189c046218118840461c010c9e04321810c400402d01009c0492800de9e037a200d89e0362180d29c034a100d26c0349600cc9c0331b00c08403928009e9e027a2809e88026278098860261f8098720261c00929e024a180926e02496008c860231b808c560231000a4a0017a7805e8a017a200589e0162180587e0161c80587001321804c6e0131000409e0102180406e0101580403e010040040fe00 i
def q41Tags := dagTraceTags q41Mask 105 (dagTagBases q41StockWords 0x3b6cf439209926c306440d0000004804872f03cbdc61c01960c00064c0b04cf9197f0c08c00d0aab8000877f2001007f0738056aaa000b0e0cfb05a04077220006811b3818b423544000802d8aa03510212002007de100a6633aebdd 0x49083409008125a282440a0000220452042100895a41001900c0064416304c2109520a08400a0aa240c056c72001002a0420050aaa0248320cf705a04059a3000501133818b42354400080060aa02201c52102007b0100a663124888 105) 11 q41Data
def q41States := dagTrace q41Mask q41StockWords 11 q41Data
def q41Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q41Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q41MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [1]), q41Move0Map, q41Move0Inverse)]
def q41Moves := dagMoves q41MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Autos : DagMovesOK q41Mask q41Goal 256 q41Moves := dagMovesOfCheck (by decide +kernel)
def q41Check := dagCheckNode q41Mask q41Goal q41Chart (dagKnownCloses q41Goal q41Cuts) 442 q41States q41Moves q41Links q41Sample q41Tags
def q41RootAt (token : Nat) : Bool :=
  let s := rootState q41StockWords 11 token
  !dagAllowedRoot q41Witnesses s.2.1 || dagLocal q41Mask q41Goal q41Chart (dagKnownCloses q41Goal q41Cuts) s ||
  dagRef 442 q41States q41Moves q41Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41RootBlock0 : treeBlock 0 64 q41RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41RootBlock64 : treeBlock 64 64 q41RootAt = true := by decide +kernel
theorem q41RootVerified : treeBlock 0 128 q41RootAt = true := (@treeBlock_merge 0 64 64 q41RootAt q41RootBlock0 q41RootBlock64)
theorem q41Roots : dagCheckRoots q41Mask q41Goal q41Chart (dagKnownCloses q41Goal q41Cuts) q41Witnesses (dagRef 442 q41States q41Moves q41Links 0) q41StockWords 11 = true := q41RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block0 : treeBlock 0 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block8 : treeBlock 8 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block16 : treeBlock 16 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block24 : treeBlock 24 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block32 : treeBlock 32 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block40 : treeBlock 40 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block48 : treeBlock 48 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block56 : treeBlock 56 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block64 : treeBlock 64 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block72 : treeBlock 72 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block80 : treeBlock 80 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block88 : treeBlock 88 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block96 : treeBlock 96 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block104 : treeBlock 104 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block112 : treeBlock 112 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block120 : treeBlock 120 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block128 : treeBlock 128 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block136 : treeBlock 136 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block144 : treeBlock 144 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block152 : treeBlock 152 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block160 : treeBlock 160 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block168 : treeBlock 168 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block176 : treeBlock 176 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block184 : treeBlock 184 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block192 : treeBlock 192 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block200 : treeBlock 200 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block208 : treeBlock 208 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block216 : treeBlock 216 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block224 : treeBlock 224 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block232 : treeBlock 232 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block240 : treeBlock 240 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block248 : treeBlock 248 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block256 : treeBlock 256 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block264 : treeBlock 264 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block272 : treeBlock 272 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block280 : treeBlock 280 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block288 : treeBlock 288 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block296 : treeBlock 296 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block304 : treeBlock 304 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block312 : treeBlock 312 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block320 : treeBlock 320 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block328 : treeBlock 328 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block336 : treeBlock 336 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block344 : treeBlock 344 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block352 : treeBlock 352 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block360 : treeBlock 360 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block368 : treeBlock 368 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block376 : treeBlock 376 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block384 : treeBlock 384 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block392 : treeBlock 392 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block400 : treeBlock 400 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block408 : treeBlock 408 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block416 : treeBlock 416 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block424 : treeBlock 424 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block432 : treeBlock 432 8 q41Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Block440 : treeBlock 440 2 q41Check = true := by decide +kernel
theorem q41Verified : treeBlock 0 442 q41Check = true := (@treeBlock_merge 0 224 218 q41Check (@treeBlock_merge 0 112 112 q41Check (@treeBlock_merge 0 56 56 q41Check (@treeBlock_merge 0 32 24 q41Check (@treeBlock_merge 0 16 16 q41Check (@treeBlock_merge 0 8 8 q41Check q41Block0 q41Block8) (@treeBlock_merge 16 8 8 q41Check q41Block16 q41Block24)) (@treeBlock_merge 32 16 8 q41Check (@treeBlock_merge 32 8 8 q41Check q41Block32 q41Block40) q41Block48)) (@treeBlock_merge 56 32 24 q41Check (@treeBlock_merge 56 16 16 q41Check (@treeBlock_merge 56 8 8 q41Check q41Block56 q41Block64) (@treeBlock_merge 72 8 8 q41Check q41Block72 q41Block80)) (@treeBlock_merge 88 16 8 q41Check (@treeBlock_merge 88 8 8 q41Check q41Block88 q41Block96) q41Block104))) (@treeBlock_merge 112 56 56 q41Check (@treeBlock_merge 112 32 24 q41Check (@treeBlock_merge 112 16 16 q41Check (@treeBlock_merge 112 8 8 q41Check q41Block112 q41Block120) (@treeBlock_merge 128 8 8 q41Check q41Block128 q41Block136)) (@treeBlock_merge 144 16 8 q41Check (@treeBlock_merge 144 8 8 q41Check q41Block144 q41Block152) q41Block160)) (@treeBlock_merge 168 32 24 q41Check (@treeBlock_merge 168 16 16 q41Check (@treeBlock_merge 168 8 8 q41Check q41Block168 q41Block176) (@treeBlock_merge 184 8 8 q41Check q41Block184 q41Block192)) (@treeBlock_merge 200 16 8 q41Check (@treeBlock_merge 200 8 8 q41Check q41Block200 q41Block208) q41Block216)))) (@treeBlock_merge 224 112 106 q41Check (@treeBlock_merge 224 56 56 q41Check (@treeBlock_merge 224 32 24 q41Check (@treeBlock_merge 224 16 16 q41Check (@treeBlock_merge 224 8 8 q41Check q41Block224 q41Block232) (@treeBlock_merge 240 8 8 q41Check q41Block240 q41Block248)) (@treeBlock_merge 256 16 8 q41Check (@treeBlock_merge 256 8 8 q41Check q41Block256 q41Block264) q41Block272)) (@treeBlock_merge 280 32 24 q41Check (@treeBlock_merge 280 16 16 q41Check (@treeBlock_merge 280 8 8 q41Check q41Block280 q41Block288) (@treeBlock_merge 296 8 8 q41Check q41Block296 q41Block304)) (@treeBlock_merge 312 16 8 q41Check (@treeBlock_merge 312 8 8 q41Check q41Block312 q41Block320) q41Block328))) (@treeBlock_merge 336 56 50 q41Check (@treeBlock_merge 336 32 24 q41Check (@treeBlock_merge 336 16 16 q41Check (@treeBlock_merge 336 8 8 q41Check q41Block336 q41Block344) (@treeBlock_merge 352 8 8 q41Check q41Block352 q41Block360)) (@treeBlock_merge 368 16 8 q41Check (@treeBlock_merge 368 8 8 q41Check q41Block368 q41Block376) q41Block384)) (@treeBlock_merge 392 32 18 q41Check (@treeBlock_merge 392 16 16 q41Check (@treeBlock_merge 392 8 8 q41Check q41Block392 q41Block400) (@treeBlock_merge 408 8 8 q41Check q41Block408 q41Block416)) (@treeBlock_merge 424 16 2 q41Check (@treeBlock_merge 424 8 8 q41Check q41Block424 q41Block432) q41Block440)))))
theorem q41Blocks : treeBlock 0 442 q41Check = true := q41Verified
theorem q41Known : Known q41Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q25Stock) q9Stock) q37Stock) q33Stock) q19Stock) q2Stock) q10Stock) q34Stock) q3Stock) q15Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q41Stock : Lower q41Mask q41StockWords q41Goal 12 := by
  apply lowerDag _ _ _ _ q41Autos _ _ _ q41Known _ q41Roots q41Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q41StockWords; decide +kernel
  · decide +kernel
  · simp only [q41Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def q42Mask : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
abbrev q42Goal : Nat := qGoal &&& q42Mask
abbrev q42StockWords : List Nat := projectDAGStock q42Mask qBase [0, 1, 2, 4, 5, 6, 7]
def q42Fact : (Nat × List Nat × Nat × Nat) := (q42Mask, q42StockWords, 11, q42Goal)
def q42Cuts : List (Nat × List Nat × Nat × Nat) := [q35Fact, q2Fact, q5Fact, q29Fact, q33Fact, q30Fact, q11Fact]
def q42Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[18, 20, 33, 34, 65, 66, 80, 129, 130, 132, 160, 18, 7, 17, 48, 100, 144, 192, 7, 7, 7, 7, 7, 7], rfl⟩
def q42Sample : (Nat × Nat) := (0x291182c120b04825120924824520d02231120501028180e0181c06050603402291601408050081408814120d02231120500884603100a45029046034028946014402110082201080814120984822402040281601040482009040442008848041010880622180c406130184804121209422150885020140884c4021080482212, 57)
def q42Witnesses := unpackWitnesses q42StockWords [99008, 361664, 624832, 893120, 1163456, 1417360, 1689700]
def q42Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x8080808080725b5150493a0e01 0x531650c384b0e4ec38580cd52504d57112513c940d2512c940894f1a52c492d0a4b0007f 8 3 13 4 1 4
def q42Data : (Nat → Nat × Nat) := fun i => decodeNode 4 17 0x19b49416ab8725129281494464a0294f14a58a4b45258207f0 i
def q42Tags := dagTraceTags q42Mask 57 (dagTagBases q42StockWords 0x7fb301830d000000ef70704168000c0e03060c0b884fe9ffc288007bd88801bde60003c02000000d8a6e17080411a03acccc 0x1f5280830a000000496840410800080b02850c008847e9a482800043d80801b687000200000000000a6e01000411a0129669 57) 10 q42Data
def q42States := dagTrace q42Mask q42StockWords 10 q42Data
def q42MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := []
def q42Moves := dagMoves q42MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42Autos : DagMovesOK q42Mask q42Goal 256 q42Moves := dagMovesOfCheck (by decide +kernel)
def q42Check := dagCheckNode q42Mask q42Goal q42Chart (dagKnownCloses q42Goal q42Cuts) 12 q42States q42Moves q42Links q42Sample q42Tags
def q42RootAt (token : Nat) : Bool :=
  let s := rootState q42StockWords 10 token
  !dagAllowedRoot q42Witnesses s.2.1 || dagLocal q42Mask q42Goal q42Chart (dagKnownCloses q42Goal q42Cuts) s ||
  dagRef 12 q42States q42Moves q42Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42RootBlock0 : treeBlock 0 64 q42RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42RootBlock64 : treeBlock 64 64 q42RootAt = true := by decide +kernel
theorem q42RootVerified : treeBlock 0 128 q42RootAt = true := (@treeBlock_merge 0 64 64 q42RootAt q42RootBlock0 q42RootBlock64)
theorem q42Roots : dagCheckRoots q42Mask q42Goal q42Chart (dagKnownCloses q42Goal q42Cuts) q42Witnesses (dagRef 12 q42States q42Moves q42Links 0) q42StockWords 10 = true := q42RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42Block0 : treeBlock 0 8 q42Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42Block8 : treeBlock 8 4 q42Check = true := by decide +kernel
theorem q42Verified : treeBlock 0 12 q42Check = true := (@treeBlock_merge 0 8 4 q42Check q42Block0 q42Block8)
theorem q42Blocks : treeBlock 0 12 q42Check = true := q42Verified
theorem q42Known : Known q42Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q11Stock) q30Stock) q33Stock) q29Stock) q5Stock) q2Stock) q35Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q42Stock : Lower q42Mask q42StockWords q42Goal 11 := by
  apply lowerDag _ _ _ _ q42Autos _ _ _ q42Known _ q42Roots q42Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q42StockWords; decide +kernel
  · decide +kernel
  · simp only [q42Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def q43Mask : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev q43Goal : Nat := qGoal &&& q43Mask
abbrev q43StockWords : List Nat := projectDAGStock q43Mask qBase [0, 1, 3, 4, 5, 6, 7]
def q43Fact : (Nat × List Nat × Nat × Nat) := (q43Mask, q43StockWords, 12, q43Goal)
def q43Cuts : List (Nat × List Nat × Nat × Nat) := [q12Fact, q2Fact, q15Fact, q29Fact, q31Fact, q38Fact, q13Fact]
def q43Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 18, 33, 34, 40, 65, 66, 72, 80, 129, 130, 136, 3, 10, 17, 24, 48, 96, 144, 192, 3, 3, 3, 3], rfl⟩
def q43Sample : (Nat × Nat) := (0x188cc06101888603148340c0e04814040a06038060701814180d008a45805008140c070088c4222140220108860120804804120c028040a0221905068220940208804210088805018088301a0182c06094020402816010404822010402413008404420088404220c06406130c024041200824402810084140b0884c1009080481409, 58)
def q43Witnesses := unpackWitnesses q43StockWords [99008, 361664, 626880, 893120, 1163456, 1417360, 1687648]
def q43Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x70381b1d0e46e4f86928c3201 0x12c3812f4410c383125010c38a925088c386c94f4c9374892c2c34f0c337083140ef440c92c2b2500ac380892ca325082c380692c6464f44637426202404f04037020080007f 9 4 13 4 3 5
def q43Data : (Nat → Nat × Nat) := fun i => decodeNode 4 17 0x1e88ec3857a21a4b0d870492c2496080dc4010207f0 i
def q43Tags := dagTraceTags q43Mask 58 (dagTagBases q43StockWords 0x3660c0203400004ef70e0502d0003d707060a00b0601a7f806140034280000ffc1c00ad5a000002ee11546b40230140fbaebd 0x2a50a02028000044950d0502a00015584040a0080601a6ac050c00282800004a81000a15a0000020311544680230140d12488 58) 11 q43Data
def q43States := dagTrace q43Mask q43StockWords 11 q43Data
def q43Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q43Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def q43Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q43Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q43Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q43Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 7, 6, 5] 0 i.val)
def q43Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 6, 2, 7, 4, 0, 1, 3] 0 i.val)
def q43Move3Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 6, 2, 7, 4, 0, 1, 3] 0 i.val)
def q43Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 6, 2, 5, 4, 0, 1, 3] 0 i.val)
def q43Move4Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 6, 2, 7, 4, 3, 1, 0] 0 i.val)
def q43Move5Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 6, 2, 7, 4, 3, 1, 0] 0 i.val)
def q43Move5Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 6, 2, 5, 4, 0, 1, 3] 0 i.val)
def q43Move6Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 6, 2, 5, 4, 3, 1, 0] 0 i.val)
def q43Move6Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [7, 6, 2, 5, 4, 3, 1, 0] 0 i.val)
def q43MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [6]), q43Move0Map, q43Move0Inverse), ((moveSchedule qStages [1]), q43Move1Map, q43Move1Inverse), ((moveSchedule qStages [1, 6]), q43Move2Map, q43Move2Inverse), ((moveSchedule qStages [2, 26, 13]), q43Move3Map, q43Move3Inverse), ((moveSchedule qStages [14, 26, 0, 6]), q43Move4Map, q43Move4Inverse), ((moveSchedule qStages [2, 26, 13, 6]), q43Move5Map, q43Move5Inverse), ((moveSchedule qStages [14, 26, 0]), q43Move6Map, q43Move6Inverse)]
def q43Moves := dagMoves q43MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43Autos : DagMovesOK q43Mask q43Goal 256 q43Moves := dagMovesOfCheck (by decide +kernel)
def q43Check := dagCheckNode q43Mask q43Goal q43Chart (dagKnownCloses q43Goal q43Cuts) 10 q43States q43Moves q43Links q43Sample q43Tags
def q43RootAt (token : Nat) : Bool :=
  let s := rootState q43StockWords 11 token
  !dagAllowedRoot q43Witnesses s.2.1 || dagLocal q43Mask q43Goal q43Chart (dagKnownCloses q43Goal q43Cuts) s ||
  dagRef 10 q43States q43Moves q43Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43RootBlock0 : treeBlock 0 64 q43RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43RootBlock64 : treeBlock 64 64 q43RootAt = true := by decide +kernel
theorem q43RootVerified : treeBlock 0 128 q43RootAt = true := (@treeBlock_merge 0 64 64 q43RootAt q43RootBlock0 q43RootBlock64)
theorem q43Roots : dagCheckRoots q43Mask q43Goal q43Chart (dagKnownCloses q43Goal q43Cuts) q43Witnesses (dagRef 10 q43States q43Moves q43Links 0) q43StockWords 11 = true := q43RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43Block0 : treeBlock 0 8 q43Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43Block8 : treeBlock 8 2 q43Check = true := by decide +kernel
theorem q43Verified : treeBlock 0 10 q43Check = true := (@treeBlock_merge 0 8 2 q43Check q43Block0 q43Block8)
theorem q43Blocks : treeBlock 0 10 q43Check = true := q43Verified
theorem q43Known : Known q43Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q13Stock) q38Stock) q31Stock) q29Stock) q15Stock) q2Stock) q12Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q43Stock : Lower q43Mask q43StockWords q43Goal 12 := by
  apply lowerDag _ _ _ _ q43Autos _ _ _ q43Known _ q43Roots q43Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q43StockWords; decide +kernel
  · decide +kernel
  · simp only [q43Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def q44Mask : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
abbrev q44Goal : Nat := qGoal &&& q44Mask
abbrev q44StockWords : List Nat := projectDAGStock q44Mask qBase [0, 2, 3, 4, 5, 6, 7]
def q44Fact : (Nat × List Nat × Nat × Nat) := (q44Mask, q44StockWords, 12, q44Goal)
def q44Cuts : List (Nat × List Nat × Nat × Nat) := [q12Fact, q34Fact, q35Fact, q39Fact, q32Fact, q38Fact, q13Fact, q7Fact, q18Fact]
def q44Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 20, 33, 40, 65, 72, 80, 129, 132, 136, 160, 9, 5, 12, 17, 24, 48, 100, 144, 192, 5, 5, 5, 5], rfl⟩
def q44Sample : (Nat × Nat) := (0x180a0c8284002460a0062100a840c26180c848260188c02a1580c14824520d02231120501028180e0181c06050603402291601402050120d02231120510088042218048201202219060702209603100a4502904603402894601440210805022140301c028340a094020402816010408842010402413008410480088410280c0640a150c024081400824402810084180d088541009080501809, 68)
def q44Witnesses := unpackWitnesses q44StockWords [99008, 362688, 626880, 893120, 1163456, 1417360, 1689700]
def q44Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x9609609609609609609609609609609609609519419409409409319309309128e38b38b08b08b08b08a18a08918728618608248208118108108108108017f17b47837807356f46966906816446045d35855715434e64e04954273f33d23943633332d629422718a0ea095018001 0x1086508232847020232531152808c958c432c220161152b1866584302c21196104c988864c433202019330a4a084f4441310200c50fd8707ec383f9285e31669587078659253105230e0dcc6e486203d61c1da5668d2585832a3e0151e30e0d52b34492c2b1951ed570f24a0689593a4a6d0a4b0a86544e01cbbaae1dc940e92584c01c3563255a590ac6c872030377a217b0e0e00626f55c3462d1730e2a92b45435a334aa1b5570d64a06892c33632192560c52995266430194148190beab85cc38a84ad140d68b40b45955c2b9281524b0a4c9250620271a7130d309587044959204961230e07d2584b2512492810a53c792584755c2292810a4b0824a23f2501e4960eb0e2652b31692c191ac8a0cac2c62838c388a496098cac286283b2511c9284c253e252583034f12195848c506eaba3555c199280c24b05ccb620659163278a993620c401801e14aae89d570498702295b104ad07a55c3925a1a92c8c32d0601682e4a2152500949604193c1cc400d251059280224b20cc9f026200302781007c040100007f 12 4 13 7 1 5
def q44Data : (Nat → Nat × Nat) := fun i => decodeNode 7 20 0x20374ac334ac323262a3202a7a2273102718a279281f0151baae199281992816496160181501894aae13aae119281149611632104ac104a61019410aae0e61c0e02d0eaae0d9280d4960d3248d3100d1a70d1a60d9288a9280aaae0992809496099288892808496089288592805aae84aae04928044960432d843278432684aae83aae0361c034ad834ad034ab83496834960302d0392882928024960232782310029288192801496010278100f810040103f80 i
def q44Tags := dagTraceTags q44Mask 68 (dagTagBases q44StockWords 0x1ffecc1820834000001177b063860b4000d000e0c006000b060028d3fe1857000d0ae3c0001fc01c05ad50c6200a0b7984051a203804415a0fbaebd 0x219d4a1420828000041124a062060a8000d000b0a0050008060928d3541451000a0a0a400008801005a154c6200a09a2c40511042004415a0d12488 68) 11 q44Data
def q44States := dagTrace q44Mask q44StockWords 11 q44Data
def q44Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q44Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q44MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [1]), q44Move0Map, q44Move0Inverse)]
def q44Moves := dagMoves q44MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44Autos : DagMovesOK q44Mask q44Goal 256 q44Moves := dagMovesOfCheck (by decide +kernel)
def q44Check := dagCheckNode q44Mask q44Goal q44Chart (dagKnownCloses q44Goal q44Cuts) 72 q44States q44Moves q44Links q44Sample q44Tags
def q44RootAt (token : Nat) : Bool :=
  let s := rootState q44StockWords 11 token
  !dagAllowedRoot q44Witnesses s.2.1 || dagLocal q44Mask q44Goal q44Chart (dagKnownCloses q44Goal q44Cuts) s ||
  dagRef 72 q44States q44Moves q44Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44RootBlock0 : treeBlock 0 64 q44RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44RootBlock64 : treeBlock 64 64 q44RootAt = true := by decide +kernel
theorem q44RootVerified : treeBlock 0 128 q44RootAt = true := (@treeBlock_merge 0 64 64 q44RootAt q44RootBlock0 q44RootBlock64)
theorem q44Roots : dagCheckRoots q44Mask q44Goal q44Chart (dagKnownCloses q44Goal q44Cuts) q44Witnesses (dagRef 72 q44States q44Moves q44Links 0) q44StockWords 11 = true := q44RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44Block0 : treeBlock 0 8 q44Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44Block8 : treeBlock 8 8 q44Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44Block16 : treeBlock 16 8 q44Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44Block24 : treeBlock 24 8 q44Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44Block32 : treeBlock 32 8 q44Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44Block40 : treeBlock 40 8 q44Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44Block48 : treeBlock 48 8 q44Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44Block56 : treeBlock 56 8 q44Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44Block64 : treeBlock 64 8 q44Check = true := by decide +kernel
theorem q44Verified : treeBlock 0 72 q44Check = true := (@treeBlock_merge 0 40 32 q44Check (@treeBlock_merge 0 24 16 q44Check (@treeBlock_merge 0 16 8 q44Check (@treeBlock_merge 0 8 8 q44Check q44Block0 q44Block8) q44Block16) (@treeBlock_merge 24 8 8 q44Check q44Block24 q44Block32)) (@treeBlock_merge 40 16 16 q44Check (@treeBlock_merge 40 8 8 q44Check q44Block40 q44Block48) (@treeBlock_merge 56 8 8 q44Check q44Block56 q44Block64)))
theorem q44Blocks : treeBlock 0 72 q44Check = true := q44Verified
theorem q44Known : Known q44Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q18Stock) q7Stock) q13Stock) q38Stock) q32Stock) q39Stock) q35Stock) q34Stock) q12Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q44Stock : Lower q44Mask q44StockWords q44Goal 12 := by
  apply lowerDag _ _ _ _ q44Autos _ _ _ q44Known _ q44Roots q44Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q44StockWords; decide +kernel
  · decide +kernel
  · simp only [q44Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def q45Mask : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
abbrev q45Goal : Nat := qGoal &&& q45Mask
abbrev q45StockWords : List Nat := projectDAGStock q45Mask qBase [1, 2, 3, 4, 5, 6, 7]
def q45Fact : (Nat × List Nat × Nat × Nat) := (q45Mask, q45StockWords, 11, q45Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q45Stock : Lower q45Mask q45StockWords q45Goal 11 := dagShiftLower (width := 256) (moveSchedule qStages [1]) q42Stock (by decide +kernel)
def q46Mask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
abbrev q46Goal : Nat := qGoal &&& q46Mask
abbrev q46StockWords : List Nat := projectDAGStock q46Mask qBase [0, 1, 2, 3, 4, 5, 6, 7]
def q46Cuts : List (Nat × List Nat × Nat × Nat) := [q12Fact, q2Fact, q13Fact, q29Fact, q15Fact, q40Fact, q44Fact, q41Fact, q45Fact, q43Fact, q42Fact, q8Fact, q5Fact]
def q46Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 18, 20, 33, 34, 40, 65, 66, 72, 80, 129, 130, 7, 14, 17, 24, 48, 100, 144, 192, 7, 7, 7, 7], rfl⟩
def q46Sample : (Nat × Nat) := (0xc0e060a0180840a14018481c8203848482c120940e8240024308800a44228160320188c0522860380607060b00c26120b0482612094482480a8501a0d80c1028552091180c520d02231120501028180e0181c06050603402291601408050081408814120d02231120510088042218048201201048300a0102808864141a088240884603100a4502904603402894601440210301c028340a0940208804202050301a0182c06091209848224020402816010404822010402413008404420088404220c06406130c024041200824402810084180d08854180908050140b0884c1009080481409, 102)
def q46Witnesses := unpackWitnesses q46StockWords [99008, 361664, 624832, 889024, 1155264, 1425600, 1679504, 1951844]
def q46Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0xaa85542aa1550aa0d502a81531a9854c2a61521a905482a05500a805402a01500a805402a01500a8053c69e14d2a60d3029814c0a6053029814c0a42514e8a1450a20d0c68254019f8cf0e7813b19d0ce827413a09d04e827413a09d04dce6e13619a8cd426a13509994c4a6032f1970cb4652927290b478e3a31d08e847063451918c0c5c62e11708b8454a2a1132889438e1a30d0860c28a06f0037e23e11ea6f05769bac9c52db76a3b4c59cac865fcaf49746b37581ab4d546a55511a791366974492a3190907e63ca9d8ce847043621998c845e62a513208cc4151d38cdc49e2040bc83a403a001 0x11c6404731911cc38c755711d250bfbd111a07046007116f44453d96fcf4443990916042443d96faf444319090a028420cd114f44418cd104028408cd31586845557100334be3d12f6f444449c30cf704319c112f44443d11138684455710ef4441a5910cf444119610a65840a5910f8684355710895a4025610a94d4224b30755c41c9430495b41253d0292d4024b0f6f4d3d3d10fe0423cb0e0f0f443ebd94eef443b3d10fcf443ebd10fd8683ed570f80493d80f4f2f653bbd10f0f453b3d10f403f3cd570f18683bd574ed55caf3d368af442f1934b4643229882ea0423a807a88c382c8cdc883143a3d10b0941a1a4b0ae02ab63dc684f443619c484620a0bd10ac643209882d2f65a03d10d26652a990c806209fbd10a86431f9880e2f7135bd10dcf6736bd14d4f44323196bac439f30e09a3363980fce4036383d9cd8f4534bd10a4c65ae310e7ac38260cd8e3868385570dec60342594c69599e24b09602a37bdc0dd868282594cc9599da4b09402a36edd0d986827b1c4c4c659d30e09233635e1a4d586834d570cec67273194cac5b30b16672c38240cd8d0c6533b0e0ccc5932b0e08e028b261a0c955cb1b19cc6c5b3130e4c2c382300a0b8c719c30e0c00489bb0e0be0492f00f4bbb742e61a0b6f6c2cc9c4ab250293dc298c70260dc0ad2512a4940b404b2ce1a0a0c66a52598940662c3102ae9402b8100adb7427bdca92c72248dc8ab8692a61a09cf66a431989036629e1a0a555c28b19ca0c5b27b0e49cc3826e1a09955c25b19c94c5b24b0e490c382399688c658223d9484f45203d107ac651c310c6cc3820bd147ef441bb10c6ac382280fc8955c1da56c6892c21a4d46692c2161a4838681d319c64c382055747f55c1cb16c62c381f61a07b55c1e319c76c5b1d30e472c381c61a46f8681b55746b55c1a316c66c571930e462c3817bd945af4515bd124ec658f310e26c38138d943c3430d8cdc26314163d1454f448eb10e24c380e8d0c34337090c506003f17d5724895b88a4b04805b0c80ac220089724d62092c1700d43002b0800205b8691661a246c6787b0e0463670b8cdc1e31415d5745555c91316e1cc38110d6c2c337070c50538691461a04f55c13319c4ac6312316c46c391130e0429670aa5944095b0fa5663893786a4b02802a0f61a43b8680e259e1892c0de1a4358680cbd9c30f630bbd142cf440ab19a289660a01982755d09557022c5b08315c1ec390730e01a95b0624dc1692c0555741355c04316c0ec570330e40ac3882256e0693780a4b00805b0180dc0402b008020000ff 13 4 13 8 1 5
def q46Data : (Nat → Nat × Nat) := fun i => decodeNode 8 21 0x4942040e0e801c7402135d5718b0d09f55c4fc3424d5712529a9092c4892823a53d1d25a8e92c470212361a0eaab8740493801e9c00fcdaab86b86833aae995570c803c62f442f01f9480d8a70d04f55c277b81361a0976e84986824c3491e1a08eab846c652261c113164858704355c2062d9030e481870400481f0248f00f47b6e83b8681d7b60e812c6f0d034c40190200cedd0630d22f86817c340b5570598ce2cc5b1661c8b30e05b0d02b55c156338ab16c558722ac381532d0a99605407e2755c1249a88e1a4430d02155d0faae07e1a03aab81cc670e62d8730e4398701d8690dc3406d57432ab818c5b0c62b8630e4318701803f0aaae0480d4230d20f86807aae8355701b0d20b86805aae02b19c158c60ac5b0561c82b0e0152ce0a95b054ac82e1a4130d00896704c3481e1a00dece06f63037a281bd100d8cc0606603aae815570098b604c570261c8130e0092b6049370249601557406ab802c5b0162b80b0e4058700205b0101b8080ac04010020ff00 i
def q46Tags := dagTraceTags q46Mask 102 (dagTagBases q46StockWords 0x445f9ff5b3018060880d000000000800477b81c0e0100b40000e1805402380c0c0600302c18026821fe3d3ff80c150c000d0aa8133ea000001ff8071c002b55446048522006801df8880001a00e4080a0000001000db115406882b001f804100a68c33baebdd 0x22079552814020880a000000000800424b41a080100a80000618050022c0a0805003020180380517e1d34900a1504000a0aa8411a8000000950041000285545f04812200680168c8c0001400e4080200000010000c1154044693001a004100a68c31124888 102) 13 q46Data
def q46States := dagTrace q46Mask q46StockWords 13 q46Data
def q46Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q46Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 4, 5, 6, 7] 0 i.val)
def q46MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule qStages [1]), q46Move0Map, q46Move0Inverse)]
def q46Moves := dagMoves q46MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Autos : DagMovesOK q46Mask q46Goal 256 q46Moves := dagMovesOfCheck (by decide +kernel)
def q46Check := dagCheckNode q46Mask q46Goal q46Chart (dagKnownCloses q46Goal q46Cuts) 143 q46States q46Moves q46Links q46Sample q46Tags
def q46RootAt (token : Nat) : Bool :=
  let s := rootState q46StockWords 13 token
  !dagAllowedRoot q46Witnesses s.2.1 || dagLocal q46Mask q46Goal q46Chart (dagKnownCloses q46Goal q46Cuts) s ||
  dagRef 143 q46States q46Moves q46Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46RootBlock0 : treeBlock 0 64 q46RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46RootBlock64 : treeBlock 64 64 q46RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46RootBlock128 : treeBlock 128 64 q46RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46RootBlock192 : treeBlock 192 64 q46RootAt = true := by decide +kernel
theorem q46RootVerified : treeBlock 0 256 q46RootAt = true := (@treeBlock_merge 0 128 128 q46RootAt (@treeBlock_merge 0 64 64 q46RootAt q46RootBlock0 q46RootBlock64) (@treeBlock_merge 128 64 64 q46RootAt q46RootBlock128 q46RootBlock192))
theorem q46Roots : dagCheckRoots q46Mask q46Goal q46Chart (dagKnownCloses q46Goal q46Cuts) q46Witnesses (dagRef 143 q46States q46Moves q46Links 0) q46StockWords 13 = true := q46RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block0 : treeBlock 0 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block4 : treeBlock 4 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block8 : treeBlock 8 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block12 : treeBlock 12 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block16 : treeBlock 16 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block20 : treeBlock 20 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block24 : treeBlock 24 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block28 : treeBlock 28 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block32 : treeBlock 32 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block36 : treeBlock 36 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block40 : treeBlock 40 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block44 : treeBlock 44 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block48 : treeBlock 48 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block52 : treeBlock 52 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block56 : treeBlock 56 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block60 : treeBlock 60 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block64 : treeBlock 64 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block68 : treeBlock 68 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block72 : treeBlock 72 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block76 : treeBlock 76 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block80 : treeBlock 80 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block84 : treeBlock 84 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block88 : treeBlock 88 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block92 : treeBlock 92 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block96 : treeBlock 96 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block100 : treeBlock 100 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block104 : treeBlock 104 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block108 : treeBlock 108 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block112 : treeBlock 112 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block116 : treeBlock 116 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block120 : treeBlock 120 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block124 : treeBlock 124 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block128 : treeBlock 128 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block132 : treeBlock 132 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block136 : treeBlock 136 4 q46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Block140 : treeBlock 140 3 q46Check = true := by decide +kernel
theorem q46Verified : treeBlock 0 143 q46Check = true := (@treeBlock_merge 0 72 71 q46Check (@treeBlock_merge 0 36 36 q46Check (@treeBlock_merge 0 20 16 q46Check (@treeBlock_merge 0 12 8 q46Check (@treeBlock_merge 0 8 4 q46Check (@treeBlock_merge 0 4 4 q46Check q46Block0 q46Block4) q46Block8) (@treeBlock_merge 12 4 4 q46Check q46Block12 q46Block16)) (@treeBlock_merge 20 8 8 q46Check (@treeBlock_merge 20 4 4 q46Check q46Block20 q46Block24) (@treeBlock_merge 28 4 4 q46Check q46Block28 q46Block32))) (@treeBlock_merge 36 20 16 q46Check (@treeBlock_merge 36 12 8 q46Check (@treeBlock_merge 36 8 4 q46Check (@treeBlock_merge 36 4 4 q46Check q46Block36 q46Block40) q46Block44) (@treeBlock_merge 48 4 4 q46Check q46Block48 q46Block52)) (@treeBlock_merge 56 8 8 q46Check (@treeBlock_merge 56 4 4 q46Check q46Block56 q46Block60) (@treeBlock_merge 64 4 4 q46Check q46Block64 q46Block68)))) (@treeBlock_merge 72 36 35 q46Check (@treeBlock_merge 72 20 16 q46Check (@treeBlock_merge 72 12 8 q46Check (@treeBlock_merge 72 8 4 q46Check (@treeBlock_merge 72 4 4 q46Check q46Block72 q46Block76) q46Block80) (@treeBlock_merge 84 4 4 q46Check q46Block84 q46Block88)) (@treeBlock_merge 92 8 8 q46Check (@treeBlock_merge 92 4 4 q46Check q46Block92 q46Block96) (@treeBlock_merge 100 4 4 q46Check q46Block100 q46Block104))) (@treeBlock_merge 108 20 15 q46Check (@treeBlock_merge 108 12 8 q46Check (@treeBlock_merge 108 8 4 q46Check (@treeBlock_merge 108 4 4 q46Check q46Block108 q46Block112) q46Block116) (@treeBlock_merge 120 4 4 q46Check q46Block120 q46Block124)) (@treeBlock_merge 128 8 7 q46Check (@treeBlock_merge 128 4 4 q46Check q46Block128 q46Block132) (@treeBlock_merge 136 4 3 q46Check q46Block136 q46Block140)))))
theorem q46Blocks : treeBlock 0 143 q46Check = true := q46Verified
theorem q46Known : Known q46Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) q5Stock) q8Stock) q42Stock) q43Stock) q45Stock) q41Stock) q44Stock) q40Stock) q15Stock) q29Stock) q13Stock) q2Stock) q12Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem q46Stock : Lower q46Mask q46StockWords q46Goal 14 := by
  apply lowerDag _ _ _ _ q46Autos _ _ _ q46Known _ q46Roots q46Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold q46StockWords; decide +kernel
  · decide +kernel
  · simp only [q46Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def qMono : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.and, [0, 3]⟩, ⟨.or, [9, 5]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [8, 3]⟩, ⟨.or, [11, 12]⟩, ⟨.or, [11, 6]⟩, ⟨.or, [12, 7]⟩, ⟨.and, [4, 14]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [13, 17]⟩, ⟨.or, [18, 10]⟩, ⟨.and, [19, 15]⟩, ⟨.or, [16, 20]⟩], 21⟩

end PEqualNP.Outside.L_meta_35778

open PEqualNP.Outside.L_meta_35778 in
theorem PEqualNP.Outside.L_meta_35778 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates out legal _ computes
  let target : (Fin 8 → Bool) → Bool := fun x => decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 0, 7, 1, 7, 2, 7, 3, 7, 5, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
  let raw : List (BitVec 256) := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
  let goal : BitVec 256 := 0xfffffffffffffffefffffffffffefffeffffffeeffffffeefffeffeefefcaa00
  have root : Lower (fullMask 256) (raw.map BitVec.toNat) goal.toNat 14 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) q46Stock
  have fan : ∀ g ∈ gates, g.op ∈ ({.and, .or, .not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    exact legal g hg
  have hit : PEqualNP.MetaComplexity.HasCircuitSize 8 target gates.length :=
    ⟨⟨gates, out⟩, fan, Nat.le_refl _, computes⟩
  have size := hcsLower raw goal 14 target (by decide +kernel) (by decide +kernel) root _ hit
  have monoEval : ∀ x, qMono.eval (List.ofFn x) = target x := by
    intro x
    have clean : PEqualNP.MetaComplexity.FanInTwo qMono := by
      intro gate member
      simp only [qMono, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    exact hcsWitnessEval raw goal qMono target clean (by decide +kernel) (by decide +kernel) (by decide +kernel) x
  refine ⟨qMono.gates, qMono.output, ?_, ?_, monoEval⟩
  · intro gate member
    simp only [qMono, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact Nat.le_trans (by decide +kernel : qMono.gates.length ≤ 14) size
