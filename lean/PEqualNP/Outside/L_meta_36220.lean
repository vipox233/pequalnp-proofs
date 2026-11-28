import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36220

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

def moveStage0 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf0f00f0ff0f00f0f, 0), (0xf0f00000f0f0, 12)], [(0xf0f00000f0f0000, 12)])
def moveStage1 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff0000ffff0000ff, 0), (0xff000000ff00, 8)], [(0xff000000ff0000, 8)])
def moveStage2 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffff0000ffff, 16)], [(0xffff0000ffff0000, 16)])
def moveStage3 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0x9999999999999999, 0), (0x2222222222222222, 1)], [(0x4444444444444444, 1)])
def moveStage4 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xc3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c, 2)], [(0x3030303030303030, 2)])
def moveStage5 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf00ff00ff00ff00f, 0), (0xf000f000f000f0, 4)], [(0xf000f000f000f00, 4)])
def moveStage6 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffffffff, 32)], [(0xffffffff00000000, 32)])
def moveStage7 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xa5a5a5a5a5a5a5a5, 0), (0xa0a0a0a0a0a0a0a, 3)], [(0x5050505050505050, 3)])
def moveStage8 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff00ff0000ff00ff, 0), (0xff00ff00, 24)], [(0xff00ff00000000, 24)])
def moveStage9 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffff00000000ffff, 0), (0xffff0000, 16)], [(0xffff00000000, 16)])
def moveStage10 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcccc3333cccc3333, 0), (0xcccc0000cccc, 14)], [(0x3333000033330000, 14)])
def moveStage11 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcc33cc33cc33cc33, 0), (0xcc00cc00cc00cc, 6)], [(0x3300330033003300, 6)])
def moveStages : Array (List (Nat × Nat) × List (Nat × Nat)) := #[moveStage0, moveStage1, moveStage2, moveStage3, moveStage4, moveStage5, moveStage6, moveStage7, moveStage8, moveStage9, moveStage10, moveStage11]
def sBase : List Nat := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
def sGoal : Nat := 0xfeeefae8feeaf8e8
def s0Mask : Nat := 0xff
abbrev s0Goal : Nat := sGoal &&& s0Mask
abbrev s0StockWords : List Nat := projectDAGStock s0Mask sBase [0, 1, 2]
def s0Fact : (Nat × List Nat × Nat × Nat) := (s0Mask, s0StockWords, 4, s0Goal)
def s0Cuts : List (Nat × List Nat × Nat × Nat) := []
def s0Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[3, 5, 6, 3, 3, 3, 3, 3, 3, 3, 3, 3, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 1, 1], rfl⟩
def s0Sample : (Nat × Nat) := (0x201804060201402050100c0203, 6)
def s0Witnesses := unpackWitnesses s0StockWords [2564, 265220, 527362]
def s0Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x1 0x7 2 1 3 1 1 1
def s0Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s0Tags := dagTraceTags s0Mask 6 (dagTagBases s0StockWords 0x3cccf 0x28485 6) 3 s0Data
def s0States := dagTrace s0Mask s0StockWords 3 s0Data
def s0MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s0Moves := dagMoves s0MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Autos : DagMovesOK s0Mask s0Goal 64 s0Moves := dagMovesOfCheck (by decide +kernel)
def s0Check := dagCheckNode s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) 1 s0States s0Moves s0Links s0Sample s0Tags
def s0RootAt (token : Nat) : Bool :=
  let s := rootState s0StockWords 3 token
  !dagAllowedRoot s0Witnesses s.2.1 || dagLocal s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s ||
  dagRef 1 s0States s0Moves s0Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0RootBlock0 : treeBlock 0 8 s0RootAt = true := by decide +kernel
theorem s0Roots : dagCheckRoots s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s0Witnesses (dagRef 1 s0States s0Moves s0Links 0) s0StockWords 3 = true := s0RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block0 : treeBlock 0 1 s0Check = true := by decide +kernel
theorem s0Blocks : treeBlock 0 1 s0Check = true := s0Block0
theorem s0Known : Known s0Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Stock : Lower s0Mask s0StockWords s0Goal 4 := by
  apply lowerDag _ _ _ _ s0Autos _ _ _ s0Known _ s0Roots s0Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s0StockWords; decide +kernel
  · decide +kernel
  · simp only [s0Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s1Mask : Nat := 0xf000f00
abbrev s1Goal : Nat := sGoal &&& s1Mask
abbrev s1StockWords : List Nat := projectDAGStock s1Mask sBase [0, 1, 4]
def s1Fact : (Nat × List Nat × Nat × Nat) := (s1Mask, s1StockWords, 4, s1Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Stock : Lower s1Mask s1StockWords s1Goal 4 := dagShiftLower (width := 64) (moveSchedule moveStages [0, 1, 2]) s0Stock (by decide +kernel)
def s2Mask : Nat := 0x55550000
abbrev s2Goal : Nat := sGoal &&& s2Mask
abbrev s2StockWords : List Nat := projectDAGStock s2Mask sBase [1, 2, 3]
def s2Fact : (Nat × List Nat × Nat × Nat) := (s2Mask, s2StockWords, 4, s2Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Stock : Lower s2Mask s2StockWords s2Goal 4 := dagShiftLower (width := 64) (moveSchedule moveStages [3, 4, 5, 2]) s0Stock (by decide +kernel)
def s3Mask : Nat := 0xff00000000
abbrev s3Goal : Nat := sGoal &&& s3Mask
abbrev s3StockWords : List Nat := projectDAGStock s3Mask sBase [0, 1, 2]
def s3Fact : (Nat × List Nat × Nat × Nat) := (s3Mask, s3StockWords, 4, s3Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Stock : Lower s3Mask s3StockWords s3Goal 4 := dagShiftLower (width := 64) (moveSchedule moveStages [6]) s0Stock (by decide +kernel)
def s4Mask : Nat := 0x333300000000
abbrev s4Goal : Nat := sGoal &&& s4Mask
abbrev s4StockWords : List Nat := projectDAGStock s4Mask sBase [0, 2, 3]
def s4Fact : (Nat × List Nat × Nat × Nat) := (s4Mask, s4StockWords, 4, s4Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Stock : Lower s4Mask s4StockWords s4Goal 4 := dagShiftLower (width := 64) (moveSchedule moveStages [4, 5, 6]) s0Stock (by decide +kernel)
def s5Mask : Nat := 0xf000f00000000
abbrev s5Goal : Nat := sGoal &&& s5Mask
abbrev s5StockWords : List Nat := projectDAGStock s5Mask sBase [0, 1, 4]
def s5Fact : (Nat × List Nat × Nat × Nat) := (s5Mask, s5StockWords, 4, s5Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Stock : Lower s5Mask s5StockWords s5Goal 4 := dagShiftLower (width := 64) (moveSchedule moveStages [0, 1, 6]) s0Stock (by decide +kernel)
def s6Mask : Nat := 0xffff
abbrev s6Goal : Nat := sGoal &&& s6Mask
abbrev s6StockWords : List Nat := projectDAGStock s6Mask sBase [0, 1, 2, 3]
def s6Fact : (Nat × List Nat × Nat × Nat) := (s6Mask, s6StockWords, 5, s6Goal)
def s6Witnesses := unpackWitnesses s6StockWords [5642, 267785, 531466, 792580]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Stock : Lower s6Mask s6StockWords s6Goal 5 := by
  apply essentialLift (witnesses := s6Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
def s7Mask : Nat := 0xff00ff
abbrev s7Goal : Nat := sGoal &&& s7Mask
abbrev s7StockWords : List Nat := projectDAGStock s7Mask sBase [0, 1, 2, 4]
def s7Fact : (Nat × List Nat × Nat × Nat) := (s7Mask, s7StockWords, 5, s7Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Stock : Lower s7Mask s7StockWords s7Goal 5 := dagShiftLower (width := 64) (moveSchedule moveStages [3, 4, 1]) s6Stock (by decide +kernel)
def s8Mask : Nat := 0xf0f0f0f
abbrev s8Goal : Nat := sGoal &&& s8Mask
abbrev s8StockWords : List Nat := projectDAGStock s8Mask sBase [0, 1, 3, 4]
def s8Fact : (Nat × List Nat × Nat × Nat) := (s8Mask, s8StockWords, 5, s8Goal)
def s8Witnesses := unpackWitnesses s8StockWords [12824, 275480, 799754, 537618]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Stock : Lower s8Mask s8StockWords s8Goal 5 := by
  apply essentialLift (witnesses := s8Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
def s9Mask : Nat := 0x55555555
abbrev s9Goal : Nat := sGoal &&& s9Mask
abbrev s9StockWords : List Nat := projectDAGStock s9Mask sBase [1, 2, 3, 4]
def s9Fact : (Nat × List Nat × Nat × Nat) := (s9Mask, s9StockWords, 5, s9Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9Stock : Lower s9Mask s9StockWords s9Goal 5 := dagShiftLower (width := 64) (moveSchedule moveStages [7, 1]) s8Stock (by decide +kernel)
def s10Mask : Nat := 0xff00ff00
abbrev s10Goal : Nat := sGoal &&& s10Mask
abbrev s10StockWords : List Nat := projectDAGStock s10Mask sBase [0, 1, 2, 4]
def s10Fact : (Nat × List Nat × Nat × Nat) := (s10Mask, s10StockWords, 5, s10Goal)
def s10Witnesses := unpackWitnesses s10StockWords [12824, 275480, 538648, 799754]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Stock : Lower s10Mask s10StockWords s10Goal 5 := by
  apply essentialLift (witnesses := s10Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
def s11Mask : Nat := 0xffff0000
abbrev s11Goal : Nat := sGoal &&& s11Mask
abbrev s11StockWords : List Nat := projectDAGStock s11Mask sBase [0, 1, 2, 3]
def s11Fact : (Nat × List Nat × Nat × Nat) := (s11Mask, s11StockWords, 5, s11Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Stock : Lower s11Mask s11StockWords s11Goal 5 := dagShiftLower (width := 64) (moveSchedule moveStages [3, 4, 1]) s10Stock (by decide +kernel)
def s12Mask : Nat := 0x333300003333
abbrev s12Goal : Nat := sGoal &&& s12Mask
abbrev s12StockWords : List Nat := projectDAGStock s12Mask sBase [0, 2, 3, 5]
def s12Fact : (Nat × List Nat × Nat × Nat) := (s12Mask, s12StockWords, 5, s12Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Stock : Lower s12Mask s12StockWords s12Goal 5 := dagShiftLower (width := 64) (moveSchedule moveStages [7, 4, 8, 9]) s8Stock (by decide +kernel)
def s13Mask : Nat := 0xffff00000000
abbrev s13Goal : Nat := sGoal &&& s13Mask
abbrev s13StockWords : List Nat := projectDAGStock s13Mask sBase [0, 1, 2, 3]
def s13Fact : (Nat × List Nat × Nat × Nat) := (s13Mask, s13StockWords, 5, s13Goal)
def s13Witnesses := unpackWitnesses s13StockWords [22058, 281636, 547882, 808996]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Stock : Lower s13Mask s13StockWords s13Goal 5 := by
  apply essentialLift (witnesses := s13Witnesses) (cut := s4Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s4StockWords) (by decide +kernel)
  · exact s4Stock
  · decide +kernel
def s14Mask : Nat := 0xf000f000f000f
abbrev s14Goal : Nat := sGoal &&& s14Mask
abbrev s14StockWords : List Nat := projectDAGStock s14Mask sBase [0, 1, 4, 5]
def s14Fact : (Nat × List Nat × Nat × Nat) := (s14Mask, s14StockWords, 5, s14Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Stock : Lower s14Mask s14StockWords s14Goal 5 := dagShiftLower (width := 64) (moveSchedule moveStages [8]) s8Stock (by decide +kernel)
def s15Mask : Nat := 0xff00ff00000000
abbrev s15Goal : Nat := sGoal &&& s15Mask
abbrev s15StockWords : List Nat := projectDAGStock s15Mask sBase [0, 1, 2, 4]
def s15Fact : (Nat × List Nat × Nat × Nat) := (s15Mask, s15StockWords, 5, s15Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Stock : Lower s15Mask s15StockWords s15Goal 5 := dagShiftLower (width := 64) (moveSchedule moveStages [4, 1]) s13Stock (by decide +kernel)
def s16Mask : Nat := 0xf000f000f000f00
abbrev s16Goal : Nat := sGoal &&& s16Mask
abbrev s16StockWords : List Nat := projectDAGStock s16Mask sBase [0, 1, 4, 5]
def s16Fact : (Nat × List Nat × Nat × Nat) := (s16Mask, s16StockWords, 5, s16Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Stock : Lower s16Mask s16StockWords s16Goal 5 := dagShiftLower (width := 64) (moveSchedule moveStages [3, 10, 0, 8, 6]) s6Stock (by decide +kernel)
def s17Mask : Nat := 0xf0f0f0f00000000
abbrev s17Goal : Nat := sGoal &&& s17Mask
abbrev s17StockWords : List Nat := projectDAGStock s17Mask sBase [0, 1, 3, 4]
def s17Fact : (Nat × List Nat × Nat × Nat) := (s17Mask, s17StockWords, 5, s17Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Stock : Lower s17Mask s17StockWords s17Goal 5 := dagShiftLower (width := 64) (moveSchedule moveStages [3, 10, 0, 6]) s6Stock (by decide +kernel)
def s18Mask : Nat := 0x3333333300000000
abbrev s18Goal : Nat := sGoal &&& s18Mask
abbrev s18StockWords : List Nat := projectDAGStock s18Mask sBase [0, 2, 3, 4]
def s18Fact : (Nat × List Nat × Nat × Nat) := (s18Mask, s18StockWords, 5, s18Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Stock : Lower s18Mask s18StockWords s18Goal 5 := dagShiftLower (width := 64) (moveSchedule moveStages [7, 11, 1, 6]) s6Stock (by decide +kernel)
def s19Mask : Nat := 0x5555000055550000
abbrev s19Goal : Nat := sGoal &&& s19Mask
abbrev s19StockWords : List Nat := projectDAGStock s19Mask sBase [1, 2, 3, 5]
def s19Fact : (Nat × List Nat × Nat × Nat) := (s19Mask, s19StockWords, 5, s19Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Stock : Lower s19Mask s19StockWords s19Goal 5 := dagShiftLower (width := 64) (moveSchedule moveStages [7, 11, 5, 8, 9, 6]) s6Stock (by decide +kernel)
def s20Mask : Nat := 0xffffffff
abbrev s20Goal : Nat := sGoal &&& s20Mask
abbrev s20StockWords : List Nat := projectDAGStock s20Mask sBase [0, 1, 2, 3, 4]
def s20Fact : (Nat × List Nat × Nat × Nat) := (s20Mask, s20StockWords, 8, s20Goal)
def s20Cuts : List (Nat × List Nat × Nat × Nat) := [s6Fact, s7Fact, s8Fact, s9Fact, s10Fact, s11Fact, s0Fact, s1Fact, s2Fact]
def s20Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[3, 5, 6, 12, 17, 26, 3, 3, 3, 3, 3, 3, 9, 10, 18, 20, 24, 9, 9, 9, 9, 9, 9, 9], rfl⟩
def s20Sample : (Nat × Nat) := (0x301c0c068241a0506830190a05824160a054281109044021104830080c0502c120b0a01402050100c0203, 19)
def s20Witnesses := unpackWitnesses s20StockWords [12824, 275480, 538648, 800788, 1061898]
def s20Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x2c4000041800f10000000000030c3601 0x531010c535870a92cc31ac988106522314418a124b06c402314e61c324b2ec6b1620a98facc5526287029300f9404c2010001f 9 4 12 4 1 4
def s20Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0x92c1315192ca31413148029101f1013192c262023142008101f0 i
def s20Tags := dagTraceTags s20Mask 19 (dagTagBases s20StockWords 0x7ff00f81e10e331d81984f3f 0x77e08d81600b120c91100195 19) 7 s20Data
def s20States := dagTrace s20Mask s20StockWords 7 s20Data
def s20Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 4, 3, 5] 0 i.val)
def s20Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [2, 1, 0, 4, 3, 5] 0 i.val)
def s20MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [((moveSchedule moveStages [7, 1]), s20Move0Map, s20Move0Inverse)]
def s20Moves := dagMoves s20MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Autos : DagMovesOK s20Mask s20Goal 64 s20Moves := dagMovesOfCheck (by decide +kernel)
def s20Check := dagCheckNode s20Mask s20Goal s20Chart (dagKnownCloses s20Goal s20Cuts) 13 s20States s20Moves s20Links s20Sample s20Tags
def s20RootAt (token : Nat) : Bool :=
  let s := rootState s20StockWords 7 token
  !dagAllowedRoot s20Witnesses s.2.1 || dagLocal s20Mask s20Goal s20Chart (dagKnownCloses s20Goal s20Cuts) s ||
  dagRef 13 s20States s20Moves s20Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20RootBlock0 : treeBlock 0 32 s20RootAt = true := by decide +kernel
theorem s20Roots : dagCheckRoots s20Mask s20Goal s20Chart (dagKnownCloses s20Goal s20Cuts) s20Witnesses (dagRef 13 s20States s20Moves s20Links 0) s20StockWords 7 = true := s20RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Block0 : treeBlock 0 13 s20Check = true := by decide +kernel
theorem s20Blocks : treeBlock 0 13 s20Check = true := s20Block0
theorem s20Known : Known s20Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s2Stock) s1Stock) s0Stock) s11Stock) s10Stock) s9Stock) s8Stock) s7Stock) s6Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Stock : Lower s20Mask s20StockWords s20Goal 8 := by
  apply lowerDag _ _ _ _ s20Autos _ _ _ s20Known _ s20Roots s20Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s20StockWords; decide +kernel
  · decide +kernel
  · simp only [s20Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s21Mask : Nat := 0xffff0000ffff
abbrev s21Goal : Nat := sGoal &&& s21Mask
abbrev s21StockWords : List Nat := projectDAGStock s21Mask sBase [0, 1, 2, 3, 5]
def s21Fact : (Nat × List Nat × Nat × Nat) := (s21Mask, s21StockWords, 7, s21Goal)
def s21Cuts : List (Nat × List Nat × Nat × Nat) := [s6Fact, s12Fact, s13Fact, s3Fact]
def s21Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[3, 5, 6, 12, 41, 3, 3, 3, 3, 3, 3, 3, 42, 9, 33, 36, 42, 42, 42, 42, 42, 42, 42, 42], rfl⟩
def s21Sample : (Nat × Nat) := (0x542e150ac4229048a4482602030120b0201402050100c0203, 11)
def s21Witnesses := unpackWitnesses s21StockWords [22058, 281636, 547882, 808996, 1069577]
def s21Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x61 0x1620202001f 4 2 11 2 1 2
def s21Data : (Nat → Nat × Nat) := fun i => decodeNode 2 13 0x620404207c i
def s21Tags := dagTraceTags s21Mask 11 (dagTagBases s21StockWords 0x7c0f611b329b9f 0x740d201a301195 11) 6 s21Data
def s21States := dagTrace s21Mask s21StockWords 6 s21Data
def s21MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s21Moves := dagMoves s21MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Autos : DagMovesOK s21Mask s21Goal 64 s21Moves := dagMovesOfCheck (by decide +kernel)
def s21Check := dagCheckNode s21Mask s21Goal s21Chart (dagKnownCloses s21Goal s21Cuts) 3 s21States s21Moves s21Links s21Sample s21Tags
def s21RootAt (token : Nat) : Bool :=
  let s := rootState s21StockWords 6 token
  !dagAllowedRoot s21Witnesses s.2.1 || dagLocal s21Mask s21Goal s21Chart (dagKnownCloses s21Goal s21Cuts) s ||
  dagRef 3 s21States s21Moves s21Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21RootBlock0 : treeBlock 0 32 s21RootAt = true := by decide +kernel
theorem s21Roots : dagCheckRoots s21Mask s21Goal s21Chart (dagKnownCloses s21Goal s21Cuts) s21Witnesses (dagRef 3 s21States s21Moves s21Links 0) s21StockWords 6 = true := s21RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Block0 : treeBlock 0 3 s21Check = true := by decide +kernel
theorem s21Blocks : treeBlock 0 3 s21Check = true := s21Block0
theorem s21Known : Known s21Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s3Stock) s13Stock) s12Stock) s6Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Stock : Lower s21Mask s21StockWords s21Goal 7 := by
  apply lowerDag _ _ _ _ s21Autos _ _ _ s21Known _ s21Roots s21Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s21StockWords; decide +kernel
  · decide +kernel
  · simp only [s21Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s22Mask : Nat := 0xff00ff00ff00ff
abbrev s22Goal : Nat := sGoal &&& s22Mask
abbrev s22StockWords : List Nat := projectDAGStock s22Mask sBase [0, 1, 2, 4, 5]
def s22Fact : (Nat × List Nat × Nat × Nat) := (s22Mask, s22StockWords, 7, s22Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22Stock : Lower s22Mask s22StockWords s22Goal 7 := dagShiftLower (width := 64) (moveSchedule moveStages [3, 4, 1]) s21Stock (by decide +kernel)
def s23Mask : Nat := 0xf0f0f0f0f0f0f0f
abbrev s23Goal : Nat := sGoal &&& s23Mask
abbrev s23StockWords : List Nat := projectDAGStock s23Mask sBase [0, 1, 3, 4, 5]
def s23Fact : (Nat × List Nat × Nat × Nat) := (s23Mask, s23StockWords, 8, s23Goal)
def s23Cuts : List (Nat × List Nat × Nat × Nat) := [s8Fact, s14Fact, s16Fact, s17Fact, s5Fact]
def s23Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[3, 17, 26, 41, 50, 3, 3, 3, 3, 3, 3, 3, 42, 56, 9, 18, 33, 42, 42, 42, 42, 42, 42, 42], rfl⟩
def s23Sample : (Nat × Nat) := (0x1c0e8543a1c0e47032150c82432108c45429140a44229048a442231c068541a0906812190904c201100844120b0100c0203, 22)
def s23Witnesses := unpackWitnesses s23StockWords [29240, 291896, 816170, 545313, 1074194]
def s23Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x367a1006440000005500141004c40000003d03c01 0x254960a6200662838c90731a2ac381725829880118a086300c0688f0e214960362004628c30e26496c992c20c403ccac69938c315126291c0ae2813870130a01e1002408040001f 9 4 12 5 2 4
def s23Data : (Nat → Nat × Nat) := fun i => decodeNode 5 17 0xc40132b0b1a38c9c262a192c531028c502c608013081a1803c20121620118a08020203e0 i
def s23Tags := dagTraceTags s23Mask 22 (dagTagBases s23StockWords 0x3ffc00fe0fe387bc4dc1e9c8fc7f 0x3ef700b40ac3e6b444d068809c4d 22) 7 s23Data
def s23States := dagTrace s23Mask s23StockWords 7 s23Data
def s23Move0Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 4, 3] 0 i.val)
def s23Move0Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 4, 3] 0 i.val)
def s23Move1Map (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s23Move1Inverse (i : Fin 64) : Fin 64 := Fin.ofNat 64 (permuteAxes [0, 4, 2, 3, 1, 5] 0 i.val)
def s23MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [((moveSchedule moveStages [8]), s23Move0Map, s23Move0Inverse), ((moveSchedule moveStages [10]), s23Move1Map, s23Move1Inverse)]
def s23Moves := dagMoves s23MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Autos : DagMovesOK s23Mask s23Goal 64 s23Moves := dagMovesOfCheck (by decide +kernel)
def s23Check := dagCheckNode s23Mask s23Goal s23Chart (dagKnownCloses s23Goal s23Cuts) 17 s23States s23Moves s23Links s23Sample s23Tags
def s23RootAt (token : Nat) : Bool :=
  let s := rootState s23StockWords 7 token
  !dagAllowedRoot s23Witnesses s.2.1 || dagLocal s23Mask s23Goal s23Chart (dagKnownCloses s23Goal s23Cuts) s ||
  dagRef 17 s23States s23Moves s23Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23RootBlock0 : treeBlock 0 32 s23RootAt = true := by decide +kernel
theorem s23Roots : dagCheckRoots s23Mask s23Goal s23Chart (dagKnownCloses s23Goal s23Cuts) s23Witnesses (dagRef 17 s23States s23Moves s23Links 0) s23StockWords 7 = true := s23RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Block0 : treeBlock 0 16 s23Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Block16 : treeBlock 16 1 s23Check = true := by decide +kernel
theorem s23Verified : treeBlock 0 17 s23Check = true := (@treeBlock_merge 0 16 1 s23Check s23Block0 s23Block16)
theorem s23Blocks : treeBlock 0 17 s23Check = true := s23Verified
theorem s23Known : Known s23Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s5Stock) s17Stock) s16Stock) s14Stock) s8Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Stock : Lower s23Mask s23StockWords s23Goal 8 := by
  apply lowerDag _ _ _ _ s23Autos _ _ _ s23Known _ s23Roots s23Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s23StockWords; decide +kernel
  · decide +kernel
  · simp only [s23Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s24Mask : Nat := 0x3333333333333333
abbrev s24Goal : Nat := sGoal &&& s24Mask
abbrev s24StockWords : List Nat := projectDAGStock s24Mask sBase [0, 2, 3, 4, 5]
def s24Fact : (Nat × List Nat × Nat × Nat) := (s24Mask, s24StockWords, 6, s24Goal)
def s24Witnesses := unpackWitnesses s24StockWords [29240, 292920, 555060, 811553, 1069577]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Stock : Lower s24Mask s24StockWords s24Goal 6 := by
  apply essentialLift (witnesses := s24Witnesses) (cut := s18Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s18StockWords) (by decide +kernel)
  · exact s18Stock
  · decide +kernel
def s25Mask : Nat := 0x5555555555555555
abbrev s25Goal : Nat := sGoal &&& s25Mask
abbrev s25StockWords : List Nat := projectDAGStock s25Mask sBase [1, 2, 3, 4, 5]
def s25Fact : (Nat × List Nat × Nat × Nat) := (s25Mask, s25StockWords, 6, s25Goal)
def s25Witnesses := unpackWitnesses s25StockWords [29752, 292920, 555060, 816170, 1074194]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Stock : Lower s25Mask s25StockWords s25Goal 6 := by
  apply essentialLift (witnesses := s25Witnesses) (cut := s19Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s19StockWords) (by decide +kernel)
  · exact s19Stock
  · decide +kernel
def s26Mask : Nat := 0xff00ff00ff00ff00
abbrev s26Goal : Nat := sGoal &&& s26Mask
abbrev s26StockWords : List Nat := projectDAGStock s26Mask sBase [0, 1, 2, 4, 5]
def s26Fact : (Nat × List Nat × Nat × Nat) := (s26Mask, s26StockWords, 6, s26Goal)
def s26Witnesses := unpackWitnesses s26StockWords [29240, 291896, 555064, 816170, 1069577]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Stock : Lower s26Mask s26StockWords s26Goal 6 := by
  apply essentialLift (witnesses := s26Witnesses) (cut := s16Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s16StockWords) (by decide +kernel)
  · exact s16Stock
  · decide +kernel
def s27Mask : Nat := 0xffff0000ffff0000
abbrev s27Goal : Nat := sGoal &&& s27Mask
abbrev s27StockWords : List Nat := projectDAGStock s27Mask sBase [0, 1, 2, 3, 5]
def s27Fact : (Nat × List Nat × Nat × Nat) := (s27Mask, s27StockWords, 6, s27Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Stock : Lower s27Mask s27StockWords s27Goal 6 := dagShiftLower (width := 64) (moveSchedule moveStages [3, 4, 1]) s26Stock (by decide +kernel)
def s28Mask : Nat := 0xffffffff00000000
abbrev s28Goal : Nat := sGoal &&& s28Mask
abbrev s28StockWords : List Nat := projectDAGStock s28Mask sBase [0, 1, 2, 3, 4]
def s28Fact : (Nat × List Nat × Nat × Nat) := (s28Mask, s28StockWords, 6, s28Goal)
def s28Witnesses := unpackWitnesses s28StockWords [29240, 291896, 555064, 817204, 1078314]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Stock : Lower s28Mask s28StockWords s28Goal 6 := by
  apply essentialLift (witnesses := s28Witnesses) (cut := s18Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s18StockWords) (by decide +kernel)
  · exact s18Stock
  · decide +kernel
def s29Mask : Nat := 0xffffffffffffffff
abbrev s29Goal : Nat := sGoal &&& s29Mask
abbrev s29StockWords : List Nat := projectDAGStock s29Mask sBase [0, 1, 2, 3, 4, 5]
def s29Cuts : List (Nat × List Nat × Nat × Nat) := [s20Fact, s23Fact, s21Fact, s22Fact, s24Fact, s25Fact, s26Fact, s27Fact, s28Fact, s6Fact, s7Fact, s8Fact, s9Fact, s10Fact, s11Fact, s12Fact, s13Fact, s14Fact, s15Fact, s16Fact, s17Fact, s18Fact, s19Fact, s0Fact, s1Fact, s2Fact, s3Fact, s4Fact, s5Fact]
def s29Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[3, 5, 6, 12, 17, 26, 41, 50, 3, 3, 3, 3, 42, 52, 56, 9, 18, 33, 42, 42, 42, 42, 42, 42], rfl⟩
def s29Sample : (Nat × Nat) := (0x703e1a0f8703d1a0f4703c1a0f0483c1c0ec543b1c0e8543a140e8443a0c0e870390c0e468361a0d42835108cc70321a0c86032150c84432090c870311a0c46031108c4542e150b4702c1a0b0542c140b0482c050b0542b140ac70291a0a45429140a44229048a468261509848261109842260a09868251089468231508c44231088c701c1a070301c0a070701a15068301a09068141a0486870190c06412191a05828160905868150904c70111a04442110c044241104844021115038140e04834680c15030480c04830080c1502c140b0482c68060a01824060201842050481408050081442030900c12030100c0203, 107)
def s29Witnesses := unpackWitnesses s29StockWords [29240, 291896, 555064, 817204, 1078314, 1336338]
def s29Links : (Nat → Nat → Option (Nat × Nat)) :=
  dagLookupLinks 0x9f134000000000000009ee8a0000000004f6059e1ab3c2067820800000000000002778280000000013b61a7469ce60b000000000272824e4c19c59138a040000000009c4040000270430000000000000026f63cd85a9b00335f066ba14d7019ad83356140000000009a88b33a5c00004ce02000013370400004cd42999840000000004cb85000000000265424c55598985312066220cc18b97f112f71c000000000975992db425b214b4c6968852cf0800004b34200000000025941cacd79529d2a30800000000094d912980e52c1000000000128640000000000941080000000000000093e8a000024f6100000000012751a4b6d49681000012580a4ae08000092a852530a4a4080000927860000249a148ed291d032331e464080000917860000245a10000091507229040000487ca0000121c0e4360800000000121616428148443908020000241a1c82c2904852070a3fa547f01000011f90e3f00800008fa871f30800000000000000000023da3473de8e606000000000471c5000011c50a386100000000011c2040000470028df82000023742800008dc831b12000000000000000000023467000008d1031a1063382c66c10000119a06332080000000000000232c1c63c78b8bd169222d00800008b286000022c02c57820000115c0800004531000000000000000000008a505144180000450828a0820000227828000089d8313320000044bc489588000000000000008930b1183a22e0c44c4000000000222408000000001110080000443c188607100321fe0c3f810000000000000043f0287b8b0f40e1e4143c418778400000000043b03875830ea061cc243749861b50c00c00000000085b930b60616a080000859060000215e1c2b81000010ab0c000042a428492f085340000000008400a00000000000000000010762a0e618000000000000020e210000082f260000000000000082c8a0000000000000082a0b0510c0000000008258c000020901c114300000000020841c0d4d80e320000203414060280b050130e02210000080802000000000402c5000010071000000000000000000000000000007ff90fe761fca1000007f184fe1080000000000000000001fa67000007e70afcd0400003f3017e486000000000000000000000001f7c5bef027dd82000000000000000000000001f7213ec877cd30f9515f1c3be2c300000000000000000007c484f7f29efc08000000000f78180000000007b792f6e05ed810000000000f6b0400003da420000000001ebe500000000000000000003d703000000000000003d6827a59ef384de6e0bccc400000000000000000007929cf240400003c7c578f020000000003c74100000f161de2a0bc501789820000000003c3467860200001e0648000077f88efe0400003bec377b0a0000000003bd41779840000000000000077902eeb1c00003ba030000000001dce0bb84600000edf09dbc08000076e04ed90c00000000076c020000000003b5c17680eeaa99d5013a8c575006e9e09d3813a50874982e8c1dd1608000074484e8709d0c0b9f4973e02e7b05cf210000000000e7414000039c0400000000000000000007350ce5c380000396c100000e5a0400000000072a8a00001ca80b92c900000000000000392420000000000000038f0d714a6e212000000000000000e172800000000070b0200001c2a0800007080a000000000000007031400001c0a0b81017018200001c001800006ff82dfe04000037ec300000dfa05bee180000000000000000000000000000dee2400000000000000ded05bd80800000000000001bd41000006f48200001bc633788100000de105bbe10000000000ddc0c00000000000000ddb05ba83b74820000000001ba01373c16e40ed9ea9b2e3b64466c802d8f0400000000000000d7e44000035e4500000d751000000000000000000000000000006b39cd650800000000000000d57380000000000000000001aa42800000000000001a94400000000000000000000000000000d431c000000000000000000000000000000000d42040000000000000000001a64834c026978200000000034b0300000d2b040000349460000000000000000000000000000000000000069184d1929a3008000000000d1609a2a0b45010000000001a2020000000000000000000342c5685020000000000000000000d031d9c11b341000000ccb14000033107660860000197e100000657a000001954280000000000000000000000000000c9c3993218000000000c931800000000000000000000000000006431ac821000000000000000000018fa28000000000c7c04000031ec163132000000000317c362e84c5b0800000000062d020000000000000062b8600001892700000000000000000000000000000c4804000000000623820000186c8b0c8400000c310400000000000000c2c1400000000000000c2b0400000000000000c2710000000000612840000184808000060f8a0000183c08000060e82c0560000000000000000000000000000000000bfa2d7ee18000000000000017e818000000000000017e608000000000000017e01af65700000000000000000005ea0abd10c00002f40100000bcf0400002f38100000bc81978e0af1815e282000000000000005e088000000000000005dc120000000000000000000bb3140000000000000000000000000000000000000000002ea0b000000000174a1800000000000001740280000000000000000002e782000000000000000000000000b9d05720680000000000000171822db2000000000016d60ada035b382b660400002d88400000000000000000005ae8a000016b610000000000000000000000005ab88b435000002cfc4000000000167428000000000000016663acbc40000000000000000000000000000000002c84e000000000000002c783000000000163a080000589160000161e180000000000000000000000000000b042c00002c0c100000b020560208000058002000015ee4abd4200000af40400000000057982aee14000000000576040000000002ba8200000ae9040000000005730600000000000000000000000000002b941000000000000000000056b9cab87d5662aaa4a5518caa1095343aa60254b82a960551a4aa2835428aa820d4fc229ec30000000000000029dc453616a6a094d01299c153302a5e2000000000052e04a5b054b2100000000000000000000000052a88a49300000291c200000a45094880a90c1520840000000000000000000a3d1146650000051902a31054600a8b8200000a2b0c00000000051502000014520a86ce50d02a151542220000000000a0f0800000000000000a0918000000000000000000140828000000000000000000280044f89e0000000000000000000000000000000004f3169e5053c02a7782000009dc08000000000000009d714000000000000000000000002748500000000000000000004e7089c039354b269c300000000000000000004cd1a9990533008000000000996080000000004c88a99004000026304000009881130e0800004c302982113020a60010000097f052ee4000004ba06000012de2800004b70296b0d2d40a5a4100000000012cc1a584500000960040000257c10000095e040000257414aa9000000000000000000009540529c3000004a6040000000002524300000000000000000000000000000000025201000000000000000000049c2000000000024d8200000000000000000004990890e912181242044818a9000c000023e8647b868f60400000000047a828f404000023ac9000008ea051d2080000000008e21c000000000000008e00800002374346e020000000000000046d04000011b20a344800000000000000000000000000000000000000000000000000002310d45a208ab24000000000000008a12914008000044f820000000002278144c8a8980512e0800004459888a05112080000000008860d10a080000442028810c00002200143e0887a08000021dc343b028730d0e40a1c41000008700400000000043296000000000218c200000000010c408000042c92855110a0280000000000000109c100000000000000108c4000000000084504000000000000008411108008000041f0400000000000000000008371c000020d8141a8283308000020c420000000000000000000417068281901ad800000000080b0901212020100000000000000201c14010a801040000200013fe867fa0c00001fe41000007f8040000000003fb827f214fe209fc01000007ee08fd421f9c30000000000fcc09f941000007e308fb641f6423ec0200000fae09f5813e78e7ce04f9a09f2c23e50200000f9011f1c10000000000f8c0800003e2827b444f660800000000000000f5a31eb01000007ab0400001ea81000007a9040000000000000000000000000000000007a804f3e4800000000079e04f2460000000000000000000000000000078e1000001e3020000078b04f140800003c4820000000000000000000784140000000000000000000f0609de890000077904e9b6000003a60273e380000000000000000000e7a0800000000073814e52780000000000000000000000000000725100000000000000072404e249000000000000000e201000003878200000e1819bfcd000006fd08df611be8137c046f704dea100000000000000000001bb873709a6e004dbe08000036f026dd04da0680000367826ce04000000000366826ca0cd92080000364026c608d7071adc1000000000000001acc4000006b00c000000000357826ad08d58080000000006ab04d4c2800003528200000d4809a8430000000000d2089a3433448868708d0c08000000000682100000000003408200000cfe10000033b9000000cd2700000000006660c0000198c300000662040000000000000000000cbc20000000000000000000000000000000000caa48000000000000000000194440000000000ca00993c13270264d04c980992c10000064a0400000000000000646100000000000000063154000018c0131782000000000000000000000000c50380000313820000000001894200000624040000000003100861f04c3c09874130e0261b04c3409864130c0260d2c0000000000000060c04c160800003050200000c101181c13030200000000018141000000000000001804400000000000000000002f82200000000017b8200000000000000000002f508000000000000002f38600000000017981000005e5040000000002f00a5de08bba0976c22ec840000000000000000000000000000000002e79400000b9a1000002e58400000b921000000000000000b8c180000000000000000000000000000000000000000002de1400000b76096b4e2bce857318ad8395a822b40456704aca1154932a8045491ca8e11500729f0453d04a76114e812959e5280ca4629480328e085190ca1e5143032838a50310a040940410000050004000013f8227e824f5209e6113c42278024ee08000013ac3274844e02400001378226e044d51c000013501269044d1040000133830000000000000000000000004ca10000000000000004bd3400000000025d8400000970192d820000000000968112b47255844a908000000000000004a120000012783000000000000000000024c0c0000000000000000000494100000124c10000000000000000000000000000000001234623ea000000000011e8300000000008ee191d032390400000000011c0200000000008dc111a0600000466080000118c32310246104000011783000000000000000000022d08000000000113cb000000000000001130300000000008921911c2223020000088810000022104440080000000000000043b1400000000000000436140000000000000043408000010c82000004300883e88000020e064190c00000000020b840000000001054200000000000000104c22068c40b0881210000000000000008004800001fd8a0000000000fd8500000000000000000001fa040000000000000000000000007d64800001f502000000000000001f308000007ca080000000000000000000000000000000007be3000000000000000000000000000003d91878c980000000003c50478610e8e01ce8c0000072a40e501000000000072410e441000000000000000e4011bfa237d08000000000000000000000000dbce1b702368186cc10000000000000006b07000001aa86000006a61000001a8060000000000d382000003491400000d10500000000000000000001a1820000000000000000000342046609000000000000000000000000194100000000000c9c1000000000000000c88518f8631b1063018000018a0800000000000000188080000000000000000000000006182000000000030a08000000000000000000060c2000000000000000000000000181082f72c0000000000000000000000000000000000000000000000017b020000000000b9cf173020000000000000017282000005c028000000000000005be08000000000000005ba100000000002db0800000000016d022cf2c00000b381000002cc0800000b2c1000002c90800000b201163820000058c080000162820000000000b101000000000058608af46000000000000000000015e022ab4455018a9041508629d100000000000000029910000000000000000000052a2000000000000000000000000148880000000000a3c200000000000000000001458828128000000000000000000000000000013e0a000004f608000013c840000000000000000000275100000000000000000000000009c05137820000000000000000000000000000000001340e243944687800001170c22a1044c200000111862124400000000000000000000000080cf000001fe14000000000000001f8183ee0800000f69400000000000000000000000000000780d0ee0800000000000000000001d714000000000000001be6400000000000000000000000000000de82000003626000000d7060000035a0800000000000000354186a41000001a8040000069c1000001a604000000000000001a30c000006881000001a10400000680100000184700000060c100000000002fc285f020bd0400000000005e410000000000000005d83000001683800000000000000000000000000000b382000002cc0856cb0ac06000000000000000aa86000000000000000aa02000000000000000a88613a5c0000000000000000000000000000000000000025e5800000000000000254280000000001290400000000000000000000000000000940211d2c000004701000000000000000000008d8200000000004681000000000023208000000000000000000041d2000001060420a0840c20810210104000000000000000000000000000007d0e00000000003e0207714000000000000000000000000000000000000000e42800000000000000000000000000000000000000000000000000000e3040000000000000000000000003881068240cc10000000000000000000018e280000000000000018c08000000000000001822800000000000000000002f83000000000000000000005d8600000000000000000000b80c00000000005b820000016c080000000000000000000000005a0400000000002c82000000937c1201800000000008f040000023810000008d04000000000046020851c000000000000000000000000000003f8c000000000000000000007b1000000000003d020000000000000003a8a000000e8081cc103902000000e2081c01037820000000000000000000000000000000000340e000000ce08000002d980000000000000002c0600000000000000000000531400000000000000000000000000000000000000000000000000000000000000118d00000000000000000000210802280003080001 0x4b0bd152aef4449db10d25cc3f49230e5234c38467250d152941434a4dd0b292c410190d00263f3ed98dcf406333b898ace586213679880c063432dc0cfca8e33727a0ccc98a32b2008c7c60a31b1110c5429031446525050b092c4b40ca92ce0110a3802120494d42ba4b0d9c6204b280a92c801e4b4c9412c0c3849d253528a94148ca4b119a64d480990519263542b188103e34d4b30d24fb432b3b80c7cd9a31430101352c604930c8104a8c02b262007c8000130a300210aac3842a24b1230c38429a4b12be04c4af00d12ba02a48bb0e11de94d42924b0d986204ad80a92b401e4b0c9412c0f4e49b310522cc38477253519094143424dd0a292c40e9904fb26373b798acd966202fd8d04a8a3372618cac7fe31f0a28c512b801a4ac803922af44433b10d0a0c383ec250cedc93736524b0a8864326118dc7fc62b0a218812a6336427b0e0d9292c4ab00d92aa02a0a18c512a6f4448a30e0fae3373640c50a860371fe004c4420090a1002109c92c4a7b0e109a92c489bd11098c384a881312a00424a7010129a0364893d111d8c4d425b0e0d8e92c4a581092940364a480a92aef444a2310d246c39488b0e1200943475a5050cc93742524b10666433eb18dcf3e6333b698ace566213631880c303432a10cdc9e63332608cac7f031f1820c6c4403150a08c512a80334a900a929801b4a4003c28031409f802109292c09f0c5113864044da50513494142424b128632a4a1004427a00847fa53508e92c362988128002a49f807928d25049d313528ac414a230e124492c43299351fc64146398dd1326354231880faa34d4a08d250643413e60ca4ed831f3620c50a8204d49f0124bf4037260007c7ee01310f802427600836198812780483610c50d8262049c013108a92c360188118894142224b126a32a49a0044274008421a4b0d7e62049900a926201e49dc941274f4e49cbd2526ef4449b30e124292c47199350c864146198d50846203e90d0526633d3b58c7ce5431535e8c50a8004149800f4a7202925f807c7ec01309c802125033509c0c5026e00809b0c51258f4447119051806354209880f8e3293b50c7cd7831425f007c7ea01310f002426a0084713130ed23353e30ca4ed031d35d8c5097a03525e007426800845f9904ed26354201880ece31e1fa00d47e60110998021251250493b0e11c264d45f190497a63541f98807e83353e28ca4d7431425d80787e401210e802125d250496a53925694c470193517a64149518a507c6203e20cd52523293b30c7cd7231449300a497401f1f8804c4380090990020d7092c09898810c2c4141eb0e0f8694135ba4b0a706410981880d6c6200978c50d6a6200970c5025a3144900048d6862048f013123a01e4924941246f444913139242c4246fa535178943447a5050c093541e24b10386433e118d4eca62b3949884d646202fc0d0ca6e33525c8cac7e031f1818c6c4363150958c5123e01a48e003922af4445db10d11cc4141db0e10369433b224dce5092d358a4b0bee64325c18dc7de62b181189c4346210951880d606200948c51172c4141d30e1032941357a4b0be8641094188123002648b8069072f4435730e024e92c356988024c31448abd111bac4141c30e0ec6937393a4b4d5892c25b98dc7da62b180989c432621092988121a3274848c6d228036489809d22401b355a4b024862048800a921e01e486bd10e4c92c09198812180424858078d5462010c0c51212f44354a4b042e620484013120e04248300a9234f4448cb10d22cc39488b0e11fa94346e2505170937444a4d506e92c418990d03063740018ccec462b3929884d4c62030b8d0cbe63372db8ccc96c32b1f60c7c5fe31b10b0c5424231448700cd21401b482803c240314481012423e00808f0c511fe04908e8020d4a62008e0c5023600847e0cd11f601108d0020d4862047c8079207250466b135202c4148030e10ca94d47f25051fa92c3af8d351f43494180d04d4631425a01351f004930b0104be40371f5804c42a00908c002022e314476bd111bcc383511880be23431f50c7c42831508b0c5022a00847a25211e604908a00211e20350898020bd83410890c511de00e08898811daf4446eb0e0f8263735098811a833f29b0cdc7d031f1098c54220314476003d1d093c475012421e00808700211d0c4c4738ca4d4031447300a421a00834f8c502180084723d20d3c314085802021400847125311c20290848020d3a6200840c50d3892c0839880d3692c08318811bcf4446eb0e102e6373921884d346202f58cdc7ce31f17f0c6c4243150828c5020800846da5211b4049081802020400846c0cd11ae01108080211a603d10880211a8f4434c98811a634d1080c511a404246880791ecf4547abd111e4c4347830fd1dcc39475b0e11d2943472a4fd1c693747024cd1be92d46e24b11b234346b0cfd02c3373ff8cccf7c32b3cf0c9ce4631534c0c511aa04346800fcbd40372db00cca6a02b279009c7c601317e803c41e00907e8021176c383ff18f4d2e62046130f5174c383fe98f4d2c620466007919434934a8c51172c3834a188118c9584620cf4d26314460b131182c383de0ca4d2431424e80741f800824e0071184f444602530f7633545f8ca4d2231445f00a493601d07d802117725045d3d11172c383ae990516c63d40a98d4ff863134818809603414598cf4bd23352da8cc493432907d0c5102894029980d916cc384099900a6403745a80441f20084578ca0d1e3143fd8cf115e92c4570cc515a314459b0e0ff463d347188116404c45880d116001e456007119d250466bd39196f44464b139190c38463a53d0c8941462a4fd18693545ea4c517892d45c24b105c34f3ae0d0516e33f45a0cf50243353fc8cc4f7432b3ce8c9ce423153460c5095a04145580f4bd00352da00c4a6202b24b00747c201307c0021146f4444730e110c63f3901884d1662024a8ca47c031f07b8c50d14314454252114e3493448c5112cc3d446b0e110a63d344188114a01e4463d10d0e92c445b0e0d0c620451bd1113ac4344830e5114c38416190cf726373ce18cce3e6213429880a6033724a0ca47be31f07b0c5114403745080a514001f44e0ca113601144f312513ac3844d0d24d0831424980741ea00844c0cf4d0631444ab13112ac383db8ca4d0431424900741e8008248807112cf4444a2530f6c3354498ca4d0231444900a492001d0798021120f44340188091e3290790c51118f4433fa4b091c6350789881118f4433f24b091a63507818811160354473d1111ac3944530e111063744218cce3c62133e98810f633743a8ccc9183291ef0c7c5f831b1070c541de31444118c111092c4418cc510233038e8c5110494044124b110031444019010e263c29700d88f8028443494110af4444230e11066414409900e3862043f8c510e803d29680dc8f602943f00441dc00833e0c510f263c43ca4b10f031443e24f10f692c43d0cf50ee33c33d0c508f46342440cd10dc32843800a10e201c33c8c50cf031423b80710e263c4380cf08ec02823a8ca08e631c43724b07b03314368c508e401c43ab0e10e863d33b18808e232843981310e403424280a10de01e4360071152f44453310d148c3944fb0e113294344ba4dd122933447a4b511292c4158d0d10e33743e8cccf6a32b3cd8c9ce343153388c50c2a04343b00dd0d603329600ac9e202723800747ac01317d803c41a00907680210cf25033818801d8314433c9410c6f44430b0e0eb06413da18d4cde6202540d04a563350758c501d40083370c510c6f4433698801d2314430bd10cd86200740c501ce00842f8d310bc0110730020cd662042e00790d32504343d150ccf44432b1390c8c4243130e10c092c4088d0cff033f3ab8cd50ba3313d98ca4e323153348c50bce0432d980fc94e03542d80c4a540291ea804c5f400f10600241c600842abd150a0f4441db0e10209433fba4fce3092d33424b0bcc6432d918fc7a862b17c989c41662107118810a8c3842c1924cce62042b8d241c231442ac9410a8f4e422b105074c384072504ccc92c2f199041c062042980990a401a41cbd10ccac3806fa4b109c04c42681010a0f44424b10d07ac3941c30e10549433d924dcf3493338ba4b4cc892c30a190ca5263727818cc7a462b17c189c41462106f188109e033426009d09601b424b0e1090649331988108e34906e8c5108ac3842218f4cc46204218cf41b83143d898a4cc262006d8c5108294c3d818d5080629330188107e32906d0c5107af4432fa4b01b262041cbd10cbcc3806c24b1072f4432eb0e01ae92c41dbd11074c3941c30e101a9373fb24cce2c92d32e24b0bc46372d898cc7a262b17b989c41262106b18810b2f4442b310d0a2c3942530e108c94342124dd07c93341e24b506e92c414990d0186373fa98ccf5e62b3cc989ce2a62132d9880c263432f08cdcb603332940cac9de3271e80c7c5ec31b1040c541aa31406a0c5106a01241524b01a631441380f41a400838a188104c3490688c5104a03d068002105ef54416b125058c383898c508dc01d0678021054c3838918810483490670c5104ec4d41330e104a94d41224b0e226201b80c78c1a04c41180a906925040fb135066c383eaa535064941418a4b0ebe64d418190505c63741598d50526203d70cace9831f3880c5079a04d414012d0440493060104bbe03729300ac8da01f1b7804c40c0090660021036c3840824b1034c38407a4b1032c3840724b103725040d3d11032c3840ba534eba94140aa4d501a92c3fa18c4e1e6201e10d0501633d2ea8cd46da31d0658c5102e92c1e08104ba80351b6004419400840a18f102892c40aa4b102633c3870c51021250407bd1101cc38406a4b0fe663138698807803414050cf4ba43351b58c741923142eb0d0100c3342e98d0100c92c4029881016c3840524b101204c2eb810101003440380a9008028410494103ef4e40f3d1103ac383e9250503892d40c24b102c64d3ae190502463540898ad0186203f90cc4f5a32b3a58c7ce183141df810500603d2e880d4a4a02b236007c6dc0131b400441900083ff3134feec383f798d8fce31d0638c50ff8c413fb30e0fe8941385a4b0fdc6363f30c7418c3143f58ca0fca0110628020ff60283f20070ffd2503febd10ff8c383a51904e146203fd00f4a4803723580a4fc60110620020fd43283fbc940fecc383f9a504e1292c3f10c741863143fa30e0e949413f9a4b0f586363f48ca8a460371b38074fbe01106100201820083840c501800083f62530fd862005f8020fdf2503f730e0fda92c3f59930fd46363f48d04e0e31423500a48d201d05f0020fc863c29100d88d00283d58cd8a420363f3c940fccc383f2a534fc69413f124b0fc264923518a8fc06203ef8d04f543370a58c74e0c31429000d88ce02a102802100325040030e0ffe94d3fca504ff09373faa4b0fe46413d498dce9262b3829880fe234e3f80cd8fd032a28f80dc8cc02b1b3007cfbc011102002417a00805e0c50fb125038198801763143ee00f0fb12503ea3d24fa0f443e1b0e0f8294d3ac2504f689353d924b0e8e62a381188073034128a8cd41743143eb80a81720083ea4940f9694a3cc0c94e0231405c0020e0031405b8020fa0f443e530f8f2c631359988016c3143e78130f9c01205a8020f929343e43130f9293d3e424b0f786353d89880e8c31e05a0020e8a31c3e5b124f94c383e3a530f766413e318a4f606203a20c78f8a0290598020f86f4437f9880f4e3310590c50f80f483e03d10dfc3140588020f82f443dfb120dfa3143d300c41600083de2530f7ac483dda4f0f6e94c3dcbd10f70c3e3db24f8f2a32537e0c508c601d0578020f68f4437d8c5015c0083d8a530f64f443d824f8f2862537d1880f4a3310568c50f5833c28980a4f560113d58d30a240343d61930a220353d50044f480283d21930f4ec383d32534f4a92c37c98806c831e28a00d0f4602a3edc940fb4f4f3ecbd14facf443eab138fa6c493e93108fa2c3f3e6b0e0f9894e3e224f8f8492c3df1934f746433da9904eae6353d998a4f5e6203d70d3cf5a3433d48cfcf263253a40c7ce8031e3820c54df0314305813cb9c0432d780fc72e0353d400ccf4403128800a48c401f1b1804c5ea00f10100241560083bd0c741543143cd30e0f2064c3c118d8ef231d0548c50f0234c3bc00441500083c78d60f003283c71930efe6343ce3d10f2a63537b9880f1a34c3bf0ca08c20293bb804414e0083c62530f34f443ca24d4dec92c3c59930f086423bb0c7414c3143c50cd0f1264c3cb8070f1034c3be8ca0f0e64c3cc3124f2cc383caa504f2892c39f98a8f0c34c3be0ca8ee801105280201480080518c50f1892c0510c50f1cc383c40ca4dea31423000741420083c630e0f0e62937a18801403143c524f4f1292c3c418d4f0e62039f0c7813e0083c8bd10f20c383c09904f1e6373c698d4f166203c30ca4e7a31f3798c50b9a03722f807c6c4013100802413c0083c2188013a0083bfb0e0efa3293790c508bc01d04e0020efa6403c13d10f0294c3c01908efc6403be0cd4de231422e80a48b801d04d80208bc62822d80a0ef52503bcbd10ef094d3bba504eec92c22e98a8eea6203ba0cd429631d3780c50b9804222d00a84000083d04940f3ef443cf2534f3a9433cda504f3292c3c998d4e7862b3779880f2434e3c28d30f063423bd8ca8b9604322c80ac6c201f3b980443fe00904d0020edd2503b23d10ea4c38376988071e3352228ca46ba31d04c8c50edd2503b1bd10eb0c423a8b0e0e8e642376188071c3352220ca46b831d04c0c50e8c3343a28ca0ed4c583b4a4d0ed06343a20d00ece3343b24940ec6f443aeb108ea0c38375988071a3353998cc48863291ad8c7412e3143b0b15012c0083ada4f0eba92c3a50cc4dd43143adb130eac9303ac3d10dd231404a8020e863343ab3100eaa9583a10d00ea52503a8bd10ea0c383a098d88843291ad0c741283143a780a4e9c0123a53130e7e3303a32530e8a3283a19930e8ef443a224f8e846253a0988087c0110498020e7c34c39f0cd0e7e64039e8d60e76c4839d30f0e7002421d8070e7033421d0ca06ac31c39b8160e6c04c39a810047c0283988d00882334398a4b0dd03143738c50e66c3837318806be31e3990130e6004039780d08800283b8c940ee0f4f3b7bd14edaf443b6313ced6c433b330fcecac393b130e0ec094f3afa538ebc9433ae2508eb493f3aca4dceae9363aa24ccea692d3a6a4b0e9834f3a58d0ce9233f3a40cdce8033639e0cccddc3153728c50c1404f2e4810cb5c03f28700dc9dc03339c80ac71002939a009ce5c02521c80746bc0131aa80445e800f0fe80241220083943d10e40c4d38c30e0e06942376a4d86a66290481880e4ef4438bb0e0e0494237624d86a26290479880e0064c37fa500e51250393bd10e48c4d38f3104e2cc3838a2538e1e942385a4f8dd69361a818a45e66250471880dc634236f0cd8db631e36a8c68e4c02539230e0dfa6361a70c7411a31436a0038dd464c3871900e1463c3910120e4125038fbd10e3cc383899938e3a64238e18f8df863637b98c88703291a60c745e43190460c50e3603e36d0048dd264037d98d0e3125038bbd10e2cc383892538e1a942384a4f8df493637b24c869662917898941166203710d08db231e3698c68e2892c38998d4e246203888d241143143802504e1e92c3751904e1c63538698806923412e40cd4112314385b0e0e14941384a4b0e1063638398a8e0c31d0440c50dfcc48381c940e04f44380b124e00c42359b0e0dfe92c37e9934df864137498d4df662937d188068433537c8cc4a1a3290438c50dba01e37a9930de462837a2530dea63537a188010c3143791900dee94137b24b0de664c37898a8de031d0428c50dd03403738cd0ddb2503763d10dd6c383752508dd29361a08ca4dcc32521b8c7410831436c0048106008371a4b0dc46200410020c3c02836f30e0dba3361a0004410200836db0e0db494136ca4b0db062a0040020c3a02836ab0e0da894d369a4b067e62021a8ca8da402a0a58078e59250395bd10e54c43394b0e4e4ac38391a534e4294338d2504e3293738aa4b0e2064e3861908e0a63e38218dcdf063637798c8ddc62b37298a8b8c3432858cdc9da33321a0cac6a831f19f0c745e03190fd8c540fc3143720138dc204237000d8dbe03336e00a8dae01236b003cda200e3653d10d86c4335c30e4d62c3834ba50cd1694133824dccd092c2e2990ca1463727618cc86662b0fd18840fa62031e0cccc5631b35824b0d2a6353339880d9c34903e0c50d80c41357b0e0d2894133324b0b8464103d9880d9801a3573d10ccac3803d24b0d5ac3803c8c50d94f4435bb0e4d58c38350a504cde93733224b0a1263727598cc86462b0fc98840f062031d8cccc5431b36480ccd9002a363806cd6c92c34218d4cc66203628d240ee314361c940d84f49360bd10d80c3835aa4b0d3c64d3371904d266353311880a1034135f8cf4a0c32903b0c50d7c03d34918d4cc262003a8c50d7894c3489904d766293301880d7432903a0c50d7125035bbd10d6cc4e35ab108d3a94d3402504cd893532fa4b0a0a6350399880c8233535a0068d6600e3573d10cfec4132f30e00e492c3573d10d36c4132eb0e00e292c35680d8d5404c3540130d62f44358310cd5ec3935630e0d4a94334d2504d2093733ea4d4cb892c304990cb826372d698cc86262b0fc18840e062032d0d0cca63373260cccc6432b3178c7cc5231b30f8c54d56033354806cd4e00f352a4b0d483490378c50d38c380371880d36c380369880d3ef4834e3d10d36c380361880d44f44350b0e0d4093f34f24dcd3a92d34d24b0d3233f2df8cdca0832b2750c9c3ee3150358c50c74027314003cd2494c3478cd0d2f25034b3d10d2ac4e34a30e0cdc941349a4d4d2293134824b085e3413470cf4b7c3352d60cc485831d0350c50d1a03d32880d4c96031343bd10cfec3821598a40d26203452520d0ef4433f30e08546290341880d0c0293412530cfef4433f30e08526290339880cf893c33d80f084c31c21298a0cf234c33c0cd085032833b8040cea93c3398130d16f44344b10cd10c39342b0e0d08943341a4dcd0293334024b4cfa92c3040d0ccf433733b0ccca0632b2748c9c84831d0fb0c540cc31432c810cce803733900ccc8002b31c809cc5c013313803cce1250337bd10cdcc42336b0e0cd892c2170cd4cd63312810ca40ca31433500c4c70025332bd10cbcc3803224b0ccaf4432eb0e00c692c330a530cbcf4432eb0e00c492c3343d10ccec4333330e4cc8c38331a50ccc493733024cccbe92d32e24b0c0e6432de98dcb5663328098ac9d06270fa98840c262032c0d0cc9e3373250cccc7e32b31b8c9cc5a31f3130c6ccb492c32c98d4cb062032b8d240c031432918d4ca062002f8c50ca803c32924c0ca093c32aa4f0ca692c32898d4c9e6203270cf40bc3143248d30c9004c3238d30c9292c32418d4c8e62002e8c50c98c38325a504c9492c2dd99040b86203230130c8a03632200a8c8601e320a4b0c8064131f9880c7c33102d8c50c7925031dbd10c7494d31ca504c7093531ba4b09fe63502d1880c6c04231a80a8c6801e31930e0c6232502c8c50c5ec383172504c5a92c0fa0c50c4a00e21118a0c440283111900c572503153d10c52c383142534c4e94131324b084262a0f99880c4a31e3120108c4603631080a82aa00830fb0e0c3c63630e8c740a4314367bd10d9ac43365b0e4d8cc38362250cd7a93735ca4ccd6492d35324b0d4664334c1904d1863733898d4cd262b32d9880c0c3432dd0cdcb4c33327f0cac9ce3272100c7c3e03150288c50cac04332680dcc8403331e80acc66027318007cc58013310003cc3800930a24b0c2464930498803de3140f70020c1031430a30e0c2264930398803da31430930e0c2292c3068d30c203343078ca8c1af480f60020c1292c30418d4c0e6200f58c50c352503013134c32c4130c30e0a8294d30ba4b096864d30b1904c2a635309988079a34d3070d24c183413058cacc1431f3030c509fa02b20f807c67a0130f50020beec382f324b0b8a6203020120bec92c3009904bca6202ef0d24b883142fab0e0bdc94d2f224b0b866202ff8130bfc02a2fe8078be8c382f62534bc692c2e11880bef2502fb3d24beaf442fa30e0bd694d2582504bd29352f124b07846412ee18f4baa6352e09880b4a3310f48c50bdac382e00c503d00082f6bd20be32502f83d24bdef482f73d10bd8c382f5a4b07823412ea0cd4b7e3142d200c43ce0082f4a4b0bb63312df0c50bcd2502f2bd24bc8f442f1b0e0bc492c1e01904bb463d2e918d4b7a6202d18cc43cc3142f03d50bbd2542eb1900ba66402ee30e0bb69412ed24b0b9e6362eb8d00bb232a27e00dc67801d0f28020bac92c2e99880bacc3c2e9b0f0baec3c2eaa4b0ba864d2e91880b903142e83120b9e3482e68d60b980102e5252069264c2e41900b8e0482e03d20b8b2502e23d24b86f442e130e0a109412e0a4b0b7e64d2179904b7c6352de9880b443310f20c50b7803d2dd80c4c072503013d38c00f492fe3d10bf6c382fd253ca809412fca4fcbf092d2f9a4b0be464f2f5193495a6412f418d4bce62b2f09880bbe34f1df8d04bba33f2ec0cf4ba23352e70cacb963272e48c7cb8c3152dd0c50b4203127d80ac83c01f19d804c3c60082d930e0b243402c38cd8af43342ae8ca0b6ac412d8b0e0b5a92c2d299043c46202cf0d30b0c3362bc8cd0aca32a2ae0ca0b483410f08c50b0804c2c800d0b020282ad80709103342ad0ca0b6ac382d61880b3a04c2c780d090a0282b20078ab201c2c000a0ab001c2ab98d0aac6342d94940b62c382d5a4b0b466410f01880b3834c2c70cd0ac632a2aa8ca0b360582b800a0ac201c2cd0160b1a0402b100d0afe0282b00070b3264c2b718d0b5431c2cc0d30b163342140ca0b520102cb9930b146342d40c70b5492c2d498d4b506200ef8020b5ac382d62504b5692c2d119043bc6202cb0d30b283362c48cd0afc32a2b60ca0b4e0102b58cd0a9c3282be80a0a9a01c2a60ca0ad03282d2b0e0b4894d2d1a4b0b446202be00a8ace0282af8078a9401c2cc98803ba3142cc0c50b2e6200ee0c50b3292c2cc18d4b2e6200ed8c50b3ef442cf24b0b086412ce98d4b386202cd8cacb3431f2cb0c509f402b20e807c6740130ed0020b283140ec8020b186200ec0c503ae0082c58c50b146200eb0c50b1892c2c598d4b146200ea8c50b24f442c8a4b0b206412c798d4b1c6202c68c7cb1231420e007c6720130ea002091094024399003a60082c1253090c9402c11880afa0350e900208506402be9930b0f2502c330e0b0a94d2c22530b0692c2c0993090a6402c018d8ac43292bf8c74afc3142be010483601d0e88020ae892c24424d4ae692c2b71880ad63350e80c5090e6352bb1880ad40350e78020aec94c2432500ae8f442b9a4b0ada6202b48cd439c3142b900f4adc92c21418d4ada6202b40cd439a3142b5a4b0ad46412b49880ad03142bd3d10af292c2bc190490a6352bb98acaea6212b89880ae032b2b78c7cad83142b380d49f202b20d807c6700130e60020acac382b22504ac692c2b118a8ac23362b00ca8abe04127c00dc29601d19b80443960082aba4b0ab49352ab24b0aa46202a70cd43943142a680d43920082ad24b0aa23142abbd10aac92c2a81880a983350e40c50aa492c2a898d4aa06202a58cd438e3142a724b0a9a6412a61880a963142aebd10ab892c2ad9904ab26352ac18acaaa6202aa0cacaa631f2a78c50a9403527b80ac83401f19b804c38c0082dc4940b6ec382db2534b689412d9a4dcb6092c2d798dcb5c62b2d31880b4234127b0cdc83232b19b0c7c38a3142d00138b2a04c2c980d8b100342bd80a8acc0282af0078a9201c2a24940a146200e18c50a8925029e3d10a70c3829b2534950941295a4d4a5292c1cc1904a2a635284988082c32a0e10c50a8602a0e08020a1031429fb160a7c33529e3d10a0e6202728cc425831429d8078a0c31429c3d10a38631282988038031429b3d10a08314272009437e0082098070a6601029a3120a643492920cf482401c2088ca082001c2970040a60f44297b0f8a5a33f28d8cc4a0631420c007481a01c0df0020a56f442810c5037a008294bd10a3463128098809c63250de0c50a4ec542918cf4a263292060078a440102908040a446412908104a240292922534a4664d28898d481602a2900040a3c35828c0ca037600828c1900a38c3828da504a3492c28c8d30a2833428b8ca866801d0dd0020a2401028abd10a289302898d0ca2233f2868c50372008287a4f081401c1a11900a1a63428600f081231c2854940a12f442843108a0ec382832508a0a92c2821934a0664121718d4a0462928098809c43252040c7837031428000c49fe02527e0d2466601227d01609f202827c00789ee01c2a3c940a8cf4f2a2bd14a84f442a0b138a80c4229eb0fca74c3829ca508a6e92c29a9934a62643296190494e63529518a4a506202930d3ca4a34328f8cfc72e33528e8ccca2c3312880ca4a1c31f2858c549fc31427e813c9f604327b00fc9c202520b807c80e01e199004c5de00f0e2002436e00827624b09a432a27830e09d692c26e0cd89a232a27518809c83350db0c509b602826800789d262026d00a099e01e2783d109d092c27198d436a62026f8d0899c32a26600d09b2028265007099232826c0ca09ae32827649409d6f4427525349d294127424b09c46350da18809bc34226b0ca89cc01026a80a09cac3827225349c692c271188080c32a26a00a899001e26f98809bc31426c0c509aa0290d980209ae31426c19309ae64026a99309b8f4426d99309b46402660ca49b231d26b0c509a80350d900209a5250268bd109a094d267a50499c92c266992499862a265988099432a2648c509900350a5807436200827a49409e6f4427925349e2941277a4b09dc62b27698849ce6202708cd480a32b1988c7c36031427001389ba04226980a898e01e2614940970f44251b0e092a94c1c798d488a629219988065231e0d70c5098525025bbd10950c4225130e071c63522218a486462020b0d0865031e0d68c5092664024e990093834025f316097a93424d993097863425d80d091e94c247313097125025bbd10960c42250b0e0934942246250071a63522598c4886629218988064e31e0d60c509166400d58020966c4825624f096434825798f095e92c25824b095c33c2178c50932640256313095695824c193083662825324c090864c2543d1085c3140d50020906640253310090464c20a810090294c24031308fcc40251c940944f44250b0e092e94223ea50087e62921698808283361930c7894002924f807893a94c24e00a093264c24da4c493492c20d98f493063124b98808d63312160c5082402a192804891cc3824024b08566201920c7891ac3823fa4b08546202088cd864631e24925309220282473d1091ac3824424c88fc92c21498808f43321910c78352314245193091092c243990490c6202140c50906624241a4d081e0342403d108fec3823f24b084e62023c8cc881c32a1908c788f801023a8c708f032823a0c708f031421300208ea62023a0c508e600823d24b08f26202128c508ee02823b00488e401024abd10928c38249a50c920933247a4b491892c245990c91263324298c890862b241189c90262123e98808dc34323d8ccc8c632b2308c9c8aa31f2298c6c8703152120c508e203220c00ac81a02a197804c63c0120d400208de954237190081803618b80408d001023419008d694c2350cd08d232820581088ce01023219008c8630232a4f08c664c21f0c708c034c22f0ca08b601023019008bc64022d99008c294c22f8d608ba33422e0ca08b401019718d08ac64019724f08ac93022c31208aec3c22a99308a43242288d3089c33418b00708a264018a804089c64021e8c708a694c22918d08786282280d6089e34c2268d0047032818a007089264022098d034e008224a4b034c008225b0e089434c2240d0088e3342200ca065801d0d2802062431c1888c708829301880c7061e31c220a4b044c6201870c7087a33421d80d088b2502223d10886c3822124b047c62611c189488062421f988087c33621e0c6886e31420500d8874026189804865601118500403480081848c7087094c1a098d086e6281840c7086c03021a803085694c214a50086003c213a50084c328215bd10854c38214a4b0850632213988084a3322048ca83463142110034844640219c940864f44218b0e085e94221724d885a92c21619088486402040cd8344314211809484200d20e816083804020d80a083401c20c193080c0302078d0081c640209a4f0822c3820824c881e3192070c508120082048d0082cf4420a98948286202090d0881a340206010c81603f20500448100082030d0098b2502623d3c986f45260bd10980c4f25fb10c974c3f25cb0e496cc3825aa53c96894e258a50c95a94225524fc952937253a4d894a93325224b493c92c24b19088e06402368d3c8d83432330cfc8c433722c8ccc8a832b1c40ca48983272230c9487231d21a0c5484031420f813c83c04320c80fc82e03720380d880a033195004c60e012177003c35e0090d0802033c3141ff49407def441f031347a8c381de25247569481c7a4d870492c1ae98d86a66201948cd833a31420180988040241fe98c07dcc381f4a5047a692c1a918807f402a1ff49407daf441f431347a4c381e625247309421c724d870292c1ae18d86a26201940cd83383141fe00d87f60261fc80907eac581fa18d07e63341f900d07dc0301f7c9407daf441f3b1347bcc411e8b0e07969491e1250877693d1d524f071a9361c024b06da6421ad98d86a06201938cd85d831a1720c643363141f2a5207d20241dd25207caf441a78c503340081f549407d0f441f3b0e07cc6491f219207826421dc98f475263c1bf98806d83421a70c505c600d0cc80207c464819280a07b69481920cd06463341ed24f064433419000a079494818f80d07b6f441ed30e07b26201ec0c7869a31419800a43300081f049407bef441ef30e07926491ee98f87b863d1eb98f06fc6201a60c5065e02918f00a05d600e0cb80207506481d3b1207a60301d330f07a92501e93d107a2c381e425247809421dc24f474a93c1bea4b06d66421a598805d431a1710c6432c3141e7bd5032a0081e3a4d07949481e318d063a0341db312078e63c1e3253076a6481e64940796f441e4b134790c381dba5247689481c924d870e92c1e298d86b23361a50c5063803617480383280081df18f078492c1e099347806201a48c5077c94c1b50d3066e31c1d998d07749481d918d076cc481d898a076cc381daa4d87606361a40c503260081d998f07626281d9253076064818d80a07792501ddbd10772c4d1dc30e076e9491da25207349421c8a4d870c92c1d798d875c6201ac0cd875a31e1a38c5063403617080343240081d3b0e07489360c88c5074cc381d1a4d868c6200c80c507406280c7802073e6281d3bd1074cc381a2988031c3141d0a5007426200c68020748f441d1b0e074492c1d0190073e6361a20c5065c01d0c60020756f441d530e07529411d424dc74a92c1cf18a86ca3371b00cac68631419a80dc65a02b1ce804c3400090c58020736f481cd192072c6301cc3d106843140c5002072c9401ca3120726c3c1c919507226481c7c94071cf441c6b0e07189491c5a4f47149311c4a4b06823140c4802070e9541c3252070a0581c201306f03401bb81006323281bb0d006f404004000206f404c1bc24b06ee6411bb18803e43141c14940702f441c030e06fe94d1bf25046fa92c1b499086ae62a0f8988063032a1738c685be31903f8c506f804d1bd81306f20411ba81006e802a1b980746e40110a580206e00541b38cf06da92c1b619346d662019b8cf46d43311b48c5062e01e1b399306ca6481b200f06c43581b019206be03018980a05cc00c1890ca06223281880ca061e32818680a06180281858c7046201c1aec9406b8f441adb0e06b492c1ac8d246b033d1ab8c506ac026195807461401c0c400206a40241a324f069e6481a698f06123281a2a4f06909481a4252068cc381a2a4b068862a0c38c506a72501a8bd106a0c381a725346989411a5a4b06946491a4990868e63d1a198f06846361a098a83e26201840ca830c3141a000a867e01919e0d2066603619d016067204019c00d066e01c19a992066833c199813866063c19718a065e94c19699206583301958ca05bc00c19225306243281888ca06449401880ca06429401870ca0648f44191b0e064492c190988063a33d1900cc863e33118c8c5062c01a184802063a94c18680a063632818600a06326401858c7062c64018a810045401c1893d10622c3818824b061e6201188c684543191870c5061a03d18600c461600818499006532501943d1064ec3819324b064a64218f190063834918d0cf463031418b8108628026189807461401c18400208032502003d3c7fef451fc3d107eec4f1fb310c7e2c3f1f830e47d8c381f5a53c7c694d1f0a50c7ac9411eaa4dc7a092c1e7193c79a64e1e219247866431df990877a63f1d618f473863c1cc98dc72e6361ca98cc72062b1c418a87066211b898806de34f1b70d0c6d03421b30cfc6c63371b08ccc6bc32b1aa8ca86a831519f0c5067a04f19d810c66c03f19900dc66203319500ac60e02a176803c5ca00e16e803433e0090c28020604f4417cb0e057c34c1490d004fc33612a8cd0602f4417c30e05ae34c14f0d0852234013e8cd84a833415e0d304a633415d99304a4640128990058a04013180d0605250180bd105fcc4d17e31045eec38179a4b05d862a17218a430862016d8d345ac34c1640d0858834115c8d004f83361310cd44a03341138c5060001215c0d004e833417f30e05c631d0c18c504f404c15b810051c03413880a04ee3401380cd05f8c3817918805d631e16a81304ec04014680d04da02815b01304d802815a99305a864c146190056664017cc9405f0f4417bb0e05e292c17518a85c46290c118805b434d1698d3058e3421618d0456434014d0cd45163341128c505a4058158813047e0281730c705a2058158013051404011f00a05a064c157990047a6341678d304d63401440cd04d4328167193055c64014398d05e6c3817925045e292c0c0988059a34c1568d0053a3361430cd04d232a11d0ca0598058156013047202816f0c70596058155813050a04011c00a0594058155013050804011b80d046c33413400a04660341190ca05d001011880705d8c38175a5045d492c17499245ce6201730ca84ce02a11800a05523401178cd055004013300a054e34011600d054c01c1528d00456328170004054804011500705c8c38171a5345c492c17098f45be62016f0ca854604013280a84520281610d004c03341608d0053033416db0e05b492c160010054203614b80d050402a12f00a05a892c16818803003141678c505a8c3816718802fe31416824b059e63516718802fc31416c3d105aec3816b24b04f464116a98d45a66201690cac5a231f1668c5059802b165807c5940130be802059092c163988058434c12e8cd058a0101608d3052a33416124b058262016230e058692c160013054003614a00d050202a12d80a0576c3815aa4b0574c3815a24b0576f4415d30e057094113ba4d456692c157988055231d0be0c5057092c15400442f600815abd10568c38159a4b055c6201538c742f4314157a4b04d663515718802f2314152004055292c154190454e6201530cc454a314152007857cf4415eb0e057892d15ca4b056e64113b18d456c62b159188056232b1580c7c55a31415600ac55601f155004c5460110bc002054205815001304b402814f3d1053a3140bb802053234c14b0d004b233414c0d3052a34014ca4b053062014b24b052a62014db0e053492c14b813052804014000a84ae02814830e051892c14830e05126200bb0c502ea0081440c50518c3814398802e8314144a4b051063514398802e63141493d10522c38147a4b051c64114698d45166201450c7c50c314142807c5080130b90020504058140813050004013bb1004e894c13825004f294013799002e200813ca5304e664c13ba4b04d631413925304dc94013a24b04e663513918804cc0110b800204e092c13799044dc6201350c504d0012135a5004d4640134190046201c133193045401c13f49404faf4413e30e04f694d13d25304f094113b25004ea92c13899304da64013618d847c31d1348c5047001d13380484ca0110b780204c034c12e8d004c601012f8d304b834012c0cd04c092c12f98804ba92c12e18804b292c12c18804c4c38130a4b04bc04c12d81004b403612b80d04a4c38122a4b04a2c3812224b04a4f44128b0e049e941126a4d448692c11e988046c31e1178c742dc314127a4b0498635124188045c0110b6802049a92c126190448e62011e0c5046a012124253048e940122bd10488c38121a4b047662011a0c7845a31d0b60c5048403d12080c446201011ea4b047863511d98802d6314115004046c92c11a98d44686201198cf4464314118807845e92c117190445a6201160cc445631411500784aaf4412a30e04a692d12824b049c64112598d449462b124989c48c621120188047e32b11f0c7c47431411c80ac47001f11b804c46001211480442d4008113003044ec38112a4b060b2501823d10606c3917fb0e05fa94d17da5045f493717b24b05ea63717a18ac5e06201778cdc5dc32b1768c7c5ca31e16e8c742d231416e01385b204d164813058c04215f810454404014f80dc53803614980d450603413f80ac4c802a12b00a44500281120020434f44105b0e03f492c0e1990835c6360ce98a8432f44109b134414c380fca4b03846420d698d833862a11080d838235810f316043a3340e0190043004c10d4940432f44109313441cc41104b0e03f092c0f799383d26420f118f83586360cd98a83086260b38d082ba3360ac0ca82a232610b80643563580f70d30429250109bd10424c380fb988042234e1080d283ce3420f08cf837e3360db0cc833231e0c18c682cc0420ab807835263410730e03ec6200df0cd83503280cb8c782a001a0d50d0037a334105c940414f44104b0e03ea92c0f699383cc6420f018f83786360da98c832c62a0c118982ca3420ab0ca829e3260ca8d603d834c103815040a31c0b201303143400dc8cd040603c100996040031c0c48cd03483280c40c703fc0300a7006030c6280c098902aa32800400703f800c0d198a03e40400fd49403f2f440fc30e03ee94d0fb25043ea92c0f599383c86420ef18f83706360da18c834462a0b18d082c23360ae0ca83e801d0f980643e200d0e0a5343de92c0d599343dc6410f6988032a34d0f60d043d63140f43d203d292c0f399343cc6200f28cf43c83140ee99303a06340e518a03a634c0eb8cd03a43280e48c703b864c0eb18d03906280ed99303aa6340e698a03be01c0eea4b03a66410ee18803b63140ec24b03ae6410eb18803aa3140e9a5303a464c0e824b039e6410e7188039a3140e524b03926410e4188038e3140f130e03c294d0f024b03bc6200ed0d303b23360ea0cd03a232a0e60ca039631e0e30c7037634c0e1c940384f440e0b138258c380e024b037e64d0df19043546350de98a43786200c50cd43743310dc8ca43703140ad80783663280d9993036c94d0daa4b03686200d90ca836231e0d4a50035292c0d18c5034e34c0d30cd03466400d7494035af440d630e035694e0d524d83506400c48ca434a3250d20c743443140aa00483409480c8a52033c0240c824f03346480c798f033063c0c724f03269480c9a52031a6280c69900322f440c830e031e9410c724b031862a0c38c5030e63c0cec940338f440cdb0e033294d0cba50432c92c0ca99383286490c918f431663c0c518d831262a03f988031032a0c30c502b402a0a6806430064c0be19002dc6340b88d302f63400ba8cd02e03280bf99302f46400ba18d02fc64c0bc99002e66340b598a030092c0b899042fe6200bf0c502f892c0bd99042f46200bc8c502ec92c0ba99042e86200b98c502e294c0b819302dc92c0b699042d86200b58c50308c380c1a53430492c0c098802fa34c0bc0d002ee3360b90cd02de32a0b50ca02ce92c0b319342ca6200b20cc42c63140b08c502be05800200702bac380ae0c502b60360ad00482b0c380aba5342ac92c0aa8c502a802a00180702a2c380a8250429e92c0a718a829a3140a600a82960121114940440f4410fb13c438c3f10db0e442cc3810aa53c41e94d106a50441893710424b040c64f10218fc4046370ff98cc3fa62b0fd98843e06200f50d383c63420e28cf83883370db8cd83603320d78cac34232a0cf8c7c30a31e0b48c682d004e0b101082c00360af00cc2b202a0a980782a401b0a50068288f4409c30fc262c3909530e01ee94107624dc1c492c06398fc17663705518cc13262b04818840fa6200188ccc02831b09fa50425292c08f99041c26200a38d240f831409430e022494d07024b00f6620093bd101bec3803d24b02863360a1bd1024cc3803c8c50288f4409f310c260c39092b0e023c94308825041d693706f24b01a664305d18dc15263304c18ac11e62103c18800603330098c6c28402a0a0494027ec4109f30e025e92c075193423a64107a98d41ba62005c8d3427a3490690d0416a32903b8c50278049027810425c92c08599341b862009d0cf40ec31409b3d1021464107e18d41b662005a0ca40ea314085313027125009ba53826a94c08499341f664109a18a41b46200598cd426632903a0c502632500983d1025ec4e097310821094d07925041d093506ca4b01646350399880070335096806825800e093bd101e2c4106c30e00e492c093bd1020cc4106bb0e00e292c09300d8254f44094b10c250c39092b0e0238943082a5041f4937077a4d41ac92c068990c19663706318cc12e62b04718840e06200268d0c08833701e8ccc03a32b00c8c7c02431b0030c54248033091806c24400f08d8cd024125008fb10423cc38075253423a94108e24b012c34d08d0d241a03410378c502320490258104222f44083b0e00dc62008aa520222f4408330e00da62008724f021cc4c0863d2021494c083bd1020cc3803618802089480810cd020094808bbd1422cf4408a310c226c3f08930e4220c38087a50c21a93f085a4dc21293308424b420a92c0818d0c20233f0650cdc18a3330580cac1503270468c540d631407f810c1fc03f02180dc07803301b00ac05e02700c004c02200f07e25301f693107d24b01f233d0620cc40d4314078b0e00d262007830e00d062007a25301e2f4407830e00ce62007bbd101ecc3807aa50c1e693307924b41de92c0678d0c1dc3330578cac14e3270460c540cc314017009c02000f0738d301ca04c07649401d6f4407531381d2c3807424b012a3350730cc415c3290328c501c803101680941bef4406c30e00c892c06fbd101aec38031a4b01b694c06c3d101aec3803124b01c4f44070b10c1c0c3906f30e01ba94306e24dc1b493306ca4b41ac92c067190c19263706198cc15a62b053189c11662103098800923430210cdc07633301a8cac05832700b8c7c01e31b06a49401a6c3805ca5341a4941068a4b012c64d068190419e6350671880114314066812419692c06519341926200610cc411231405f8ca017e64c063c94018cc38062a534188941061a4b0184641044188018234e0600cd817c32a020010417803c05b813016894c058b12017725005d3d10172c4e05c312416cc3805aa53816693e05924b016064d057990412a63505718a415a6200528c9412631e0438c50158031015809414464c04e8d3014234c04e0ca014064c04f8d30146f4405130e013a64105098d414062004f8ca410c31404ea5301386400554940152f44054253414e94105324b014a635042988014834e04f0d3013632a04cc940130f4404bb0e012c94e04aa4d812892c0498cd8108314049009401c00d043193010004c048494011ef4404730e011a94d046250411692c045193811264204418f810e63604298c810862a00b0c7401a319041813810403604080a80fe00e03d3d100e4c38034a5040c892c03d3d100e2c38036a5040c692c03c80a80ea94c0393d100e2c3803625040ce93503124b00dcf44036b0e00d892c034bd100d0c38033a4b00c8f44031b0e00c492c02fa4f00ba04c02c18f00ae63002a81300a804003ebd100f8c4303db0e40f0c3803ba50c0ec93703a24cc0e692d03824b00de64303599040d463703318d40ca62b030988008c34301f8cdc0743330198cac05432700d8c7c00a315030010c0bc03702e00cc0b602b02d009c0b201f02b004c0a600f0290024098641025188008e314027012009893c025252008e948028252009e941026a4b009664102498800903490230c5008892c02199340846200208cf408033101f8c5007ac3801e253407692c01d188006ec4801c24b006c64d01a98800683310198c5004e34c010813004c04c0128d3004804c0118d30050f44013b0e004264101318d404a6200120ca4046314010a5300632500183d1005e94d017250405a93501624b0056635015188005204e011013004002a00f807803ac3800e0c9403631400cb0e003094d00ba4b002c3140060038029250009bd10024c38008a534020941007a4b001c62a006988001831e005813801403600480a801000800330e000a6200020cd800631e0a43d1028cc430a2b0e4282c3809da50c27293709924cc25692d090a4b023064307e99041f063707698d41c662b06a98801983430640cdc17a3330558cac1343270488c7c0fc3150288c5008a04301f00dc07203301900ac03c02700d007c02a013003803c0040094b53d112c4c434ac30e528ec3849ea50d25e937492a4cd23692d48224b11ee643467990515463743518d50b462b41b18810423434010cdcfba3333d08cacee43273968c7cda031530d8c50c0a0432dc80dca9003327a80ac98c027202007c60c013111803c292009000802000003f 19 6 13 12 1 6
def s29Data : (Nat → Nat × Nat) := fun i => decodeNode 12 25 0x3d100064a12c632a967008cb38d2658c0552c801e964024cb1b10c0064a12b2f4e9590264ae80d25740552ba01a9590154ad007a56801d2b2c390017a24a400da5540552aa0339487a24a980aa52009929a04294d61c4a7810253406d29a01b9480214a480da52405529200f94861c000c9424f988327cc3893e1954a1004650869327c02a93f00f49f81264f928600204893c9284983d3a4c1e9326004c9387a249830e24c065526801193419ec9800aa4c403d26203d93049b800c94249929d24cf4492c4a649318a649865324d25092761c49380a649926600325091c7a248e313a47188523801292000d48e013247403d23a00e91c496800bd1241588720a02691700d48bb0e6415e89224036912013c89006e44987120a02a90f00f48780ce415e8921604290b00f485806e415e8920c04c90602148300aa41801f20a92c00192847c01264098831f0c388f8024c7fa5063e12591f03348fb008c7d8d263e003d1f20498f8321800bd16341e891a09488f3024c79b10e34006b1e2c3f8d0007477b0e6341e891d800f8ec61c46801263a92871a0c4c8e6194c7300a639927f1a0f488e449bc6825323840531c29338d0496c683d123758711ba92c8d04a446d01263686871a03348d7008c6b8cfe3400871a0f448d11a6c68810a34403d1a203f8d0320800c9422ade9d15601e8cc7a24558d2632989d156c388ab4a7c55a56231927f15633d8c449ac55bd122f987118294c8be194c5f00a62f926315692d8ab92845cbd122e587117292c8ab19fc55b0e22d402316a33d8ab61c45601322b006915801e8ac4964568cc62b462915a01c8ac01ec5598dc005e890d69488a71a4c53b10e1ac03d14ac3986b7a245000de28005314001f8a061c435b12626987113432889b008c4d8d262692870d633d89849bc35bd1224987112a94c892194c4900a62492670d6f44890496c35bd12229873114f4488b01ac45b0e22292590d692c88819bc35c9421f9e890fcc3887e320c3f24b2208c810fc64088018a43f00461f86670d693c87749643b8cf61dd2590f031487819e43b80de1ad8710d863d86c02643600d21b0c790e033c87000f43624b21b46290da01c86c019c3598d40064a10b6f4585b928433bd1216d89d0b6c4285b7a2431b0e216de890c292c85b1a642f00461786630b601e85c018c2d98ac005e8906e6498571a4c2bb10e0de4a10a4f4e852013429006a14987306ef4484b019c25813213408109a02784b00dc25b0e20dd87108e6498471a4c23a50e0dd87108663d84319ec21a4de0dd29907e62983f194c1fa4ce0dde8907a92d8377a241c30e60e1e89072c3883849641b988000402506b25082261c41125060892590446418227aa41798de089893058c3882c31ac1130e20a8c4104404b822626c11b0e208d29b04692c82301541181260886860032508037a7401bd1200d87100692d80392840cbd1206587103292c80349640b993600d25902692c81419e40998d600cc5700725080d7a2406b0e203525901a62080361c40224b201009900803480401540224b2014c4100a02880401ec018cdc0064a0fbcc387de4a6bef4941fe9e88ff4c387fa0143fd80f5fe9282fbc9377de9283fb30e1fd9258fbcc387f34963f99905f7869cfbc3367de9283f4b0e1fa5258fd26207ec3263f498d9fa4682fd232a7de9283efb0e1f7d29afbe63c7e44a0befa4b1f7cc92fbe6207df1a0bef8045f7866600203c7dc9283d13d3de89e8af452507d70153ebbd11e8989cf452507d4624bd13109e8987ef44f447ce0263e70049f39870f4494e7a2624be2b0e1f1527af9092c7c84a63e298a5f14052f8a93e7a27a23e1a4b1e89e88f7ef447c06243df9935e89890f7694c7bc49e3dd990de89e88f6cc3e7b64a63dba4f9ed8c82f44f447b4314bd13d11ec1298f6293e7b03103d10d3de88686f4464c7aa1a63d58045ea867ef440337a261c3d1a535e8d258f4664c7a40153d180c5e886560032507737a23b9a535dcd286ee6f4479c4a0bb9bd11e69258ee6c4979400e3cbb0e1e51282f2892c79431abb98d39dcde88f0cc3878631bbc330e1e38c6af0cc3878c3103c324f5e1d258f0e6357873103c38ca5e18698ee66207841a13b9bd11df1298ef864277c61c3bf9901df0c80efa33577c1953b9c941dd1e88ee894d7744a0bba24b1dd0c40ee8335774008bb98c9c0064a0e5cf4f72e7a2b974941db9e88e5cc4f72e621b973161d9d268ece63476719a3b3b0fdcb9872e5d2507637a23b1b0e1cb98a8ec294f72e4a7397250dcb9258eba94272e6263ada4fdcb926ee5cf4475849b3973101d552b0eaa93372e496b974941d39e88e9cc3874e014ba70049d39258e5c34f72e1a1b973131d2867ee5c33772e7a23a0a531d14650e8a93e7413263a19895d04c40e8233672e32039e8cd1cf86b0e7a33372e62439d30f1ce8056e5c33473502c39a8131cd4080e6a02772e61c3978131cbd258e6204072f01a3978095cb863e0032506d17a2368b10db45872da32507267a23930095c99870da2c387244a6b688121c89286da325071b7a238db0e1c6cc84e3663e71b01f38da505b4526eda32507167a238b30e1c59258da292c71131ab889881c44692e2264e6d149638698d5c34c40e1a6426d161c3832505c19258e0c6367063153830c75c18c7cda26376d192837cbd11be5892df2c426f949637cb121bf8c9adf26416f9314b7c9881be4662df26366d14a0b7824b1bc0c6ade86206f43263781901bc8c54de031d6f031936898adb464a0dccf446e661c3732509b9926cdcc3406e719a3738c95b98c54da204e6d14963711881b88084da20366d1019b68b0e1b7466cdba02a6d161c36c2505b61258db062a6d8009368803db45870da494d6d249636900a9b4801cda23150017a230e0d25b39886c3801a6cc61cb0e3d11b1c066d8e02a6c700db63b0e1870692d8a94361c92835f3d25af9e88d7cc386be19eb5f00f5af926ec3894c6ba314b5d0ca5ae9266c392506b37a2359b139acd884d6601a6b3007359a4b5871e88d4ec436a761cb53bd11ab406cd5ac386a7019b538131aa8036d4e04c6a8007b53a4b1871258d483496a4321b0e3d11a65870d3293f6997a434fa4dda6525ad32f4469b61c34da4b1a6467ed3264161c928346bd11a3589cd1ac3868d49ab46a531a49262d1a92c68d19a3478cf5a3407ad1a63761c7a23392521a29886ce4c396727a234300a5a19870ce494367249bb392531a09266ce492d6727a233f30e19f9258ce493c67b01e33d8cdd9c8698cee33467700833b8ccd9c9278cea03767202633980cd9c8c6ac3925066a7a233531099a9870cd492c66a198b3500c59a8c56c38f4465c621b2e30e5971e88ccac3865c4a1b2e24dd971298cc293365c496b2e3d11975870cba92c65c31030e24b195cc6acae6206571a4b2b810d871278c9c03c65449632724c1948c6ac9c93c6503103270cf593806ec38c386434a0b21a4b190d258c8e635647310323813190c06cc8602a64300f32180cd871258c7c64163e31031f0cc58f8056c392506347a231a25358d1282c6893563449631a01098d0054c6801e634013b0e30e18c464ac6201f61c61c316a5058b5258c5a01361c928310bd11885870c4294d6214a0b10a4b188463cc4204262101b3109901888054c4200f61c61c30e98d987463ac3a00961c18a000c941819882c0cc386064963031905818c6ac0cc3861431030330e183d258c1e33460f1953078d25819e90c1a341606195b030c7d819258c0e6356073103038c518180860020486049282dd3d396e8c82c02f495ba0262fe80a97f403cbfaf445ba61c2dd253d6e927eb7492d5ba9282fa3d257d1e88be8c385f44962dd193d6ea4a0bd6f495eb7a42f5bd117ade90bdac385eb4962f599356e9258bd26355ba315add4941789e92bc4f445e261c2f124b1788c40b74f545e01a7add495177867eb74c385d94a0aeca4b1764654bb233d5ba61e2e930f1759258ba464d5d261e2e9988174866ab74c485cf1a42e78cad6e86b0b980105cc193add252172863eb746405c70242e38c556ea4a0b76f495bb7a22ddb0e16ed258b76f485c0326add98d56ecc40b7603d5bb018add8c516e806e00325054961c2a4a535525870b6a94154949baa4c9416c5870b6292c54931baa498ad525870b4e9415a74962d3a4b16a0c6ab506205a80082d39881525870b4494d5a24962d11881688682a9204e5497a22cb24b1658c6ab2c620596195acb0c7d659258b2e6355973102cb8c51658098a9231459401b2a4bd11625258b1264158931aac4988162463eb1292c58a31aac51881628628b120345499282be30e15f129aaf894c57c4962be1881608c98af863657c18eabe0c515f0c98afa04157c0152a4bd1159d258ace641567315ab3a5315d8c42acef445724962b900f55c8c40ace32b56718fab3a4b15b4c40ada3145674962b419055a0c40ad031456801aab380a1525870abe94155f4962af98a957c66cabe32a55f020aaf8079525e88a9492c54a320aa524b1568c6aa9462b54a7a22ab24b1558c40a9432b54a18faa524b1540c6aaa062055018a2a524b152cc82a9662054b18a2a580d5528038a9203300192827b3d3d3d9e8a9ed2505430152a1bd113d989c9ecc424f662c29f0cd54f987e9ecf4453b00f29db0e13d92849ecf4453849627b3d114d8c9a9ecc485320082998d254c8c869ecf4452d61f29680414b867ea5a6414f67a229598a53d9e88a526204f662a2938d3d3d86869ec94d520326a901905484082a4201052019fa7b0d614786669ecc385174a0a8ba4b145c698a2e64051819528b8cc53d9e88a229305111a1a88804144867ea223294f649e2878c7d3d8c68a1803c50c18aa7b49413fde889fec424ff61c27fa5093fd2589fe64d4ff320a7f98a53fcc409fe0314ff012a7f8c513d809e9ec3494fc021a7b01613dc0509ee01e4f700e27b80fd3d80560032504c77a2263a53531d28298ef444f049626398ad31cc4298f2504e87a227425353a12829d092c4e831026380413998709c494d4e2496271188138866a98e04e4c731026f0c5137808498ef444d432626a190135063a9a864c4d732026b8c51350c989aa0354d4015263c941321e8899094d4c84a0a6424b1320c9299062a4c83102640ca93206289900354c800f263809c0064a080af4f4057a2a02c941309e8880ac4f405621a02b1612ed2689766344bb01a25db0fd01587280b2504b77a225bb0e101529e80a94e4056242590d212c928680a92c4ae4962578cf12b928480ac4c4ab4ac255a4fd01526e80af444a849b202b10129926680a92d40592824fbd1127d87093e02949f00f24fa4b101529893802849c498a4ba4b125cc9893263149731024b9909015e888e2c384714a1a38a531244050922933471496a38bd1123587091a92c471321a389931228c668e292c486320a431881218c648e262b47149a241989d1c4c428e2f4447e61c23f24b11f8c408e201047c199a38a4b11c8c408e431447801423900491c8c408e631447300423980411c80648e26404054aa23719011b869e80a3434054a62338cd119c6508ce6404680082338cfd0152788c66304643262318cdd0152988b46404601ac22d19011786688b432845a32022d804116866680ac4845561e22aa4c1158c988aa32b4054a622698d1134c808a235844d1a6226990113868089a32740561c2238d3111d25889234044719a2238c950164a0874f4443a61c21d24b10e925888262443a31021d0cd90e866887a31a43a01a21d80990e863a80a94c43531421a80c10d401886a315405928210bd1108587084203c4304a1210a4d90852588426424217a2212b0e109525884a6324253102128ca109866484a640421012a10990108801a842314405027a02810d0140b083404041a01420d007106807e80a64c41801ba02bd11020c4a81062040849e2098d0902187081c93240e18ca070c5103868081004340801fa04004502068081200840801b2028d0101806680a01f001013201009100a4a060ef4f3077a2983c940fe4c607fa0363f90131fc80a8fe80487f2f44307627983b10cc1d8b07e46343f219a1f900d0fc987e60ec393079281f680c0fb9e887dac383074a7983c940f900487d2f443e461c1f21924f91e887ca6483e44a69839920f8928660f2503d77a21ebb0e0f5cc7c7ae63d3d77a21ec30e0f60c407b031e3d831e1eba504c1d26e60f2503d10181e9bd10f458707a292c3077aa1e7993cc1cc9c60f2503c57a21e2a520f2989a78ac383c531e1e3a530f18c6c78a649307321983a4b0f00c9a7806203c0321183a530ef8c7e60f2503ad7a21d6a520ee989a75ac383ad4a49d6b0e0ed526c76a9483ad31e1d9a530ec0c507626483b031b1d69880eb463c75a63d3077a21ceb0e0e7528273a93739d7a21d330e0e9925873af4439f61c1cfa4b0e7cc4074264039f31b1cf98a8e7402673a63c3077a41cd1920e68c6e60ef4439831b183a500e58c6660ec4839161e1c89950e44c9072262b3079281c4bd10e2587071294938949e9c4a4c4e2525871262a3074aa1c22520e100b070804c384310983c940dc9e886e4c383724a69b92504dc92586e404d3720261b90130de80826e492c3763209bb1880dd80806e402a37200e9b90044dc8c4060e0543701a79838d0cc1d2586d264d3693101b48cc4da46286d23423073261b38cfcc1cc906c803c36419b9838d60d8866660e64835f0181af8cacc1e4a06acf4435661c1ab24b0d586926ac33d35618a1ab0098d5865460e31530792819f8090d49e8867ec3833f3241a7a534cfcc7869a94133f49619f9924cfcc8467e94834831e99fb0e0d1125868862a34431e19f98d8cfcc5467e02a33f00c99f8c50c1c09e60e34833c0219838160cdc08066e03433700e19b80fcc1cc9066633c33302719980dcc1c06660e63c3304a619598a0cb8c9065633032b19419580acc1e4a0610f4430861c18424b0c20c84610f4431f61c18fa4b0c7cc4063e33231f19898f9900c2129863a34930819418d8cf4c20c806323143080211841900c5408062a02630800e9843d10c2d87061692c30b3101858c50c2c07a61603130b0041858070c20c80612008308015183804c0064a0448f4422461c9124940c01e8860001230061c11230e0bf929a448c382fc4a091224dc8924a05eef442f761c17ba4b0890c6e44862b22461c178a504bc52585e262022419b9120cac89063e448c382e64a097324b0b98c925cc0102e83101730ca8b9863c448c382de4a696f24b0b78c7a5bc0102e031016f0ca8b7863a44804e22461c16d24b0b6809a448f442ca61c16524b0b28c6a594c382d43101650cacb2863e59492c2ce31a9671880b3862859402b2ca00f965004cb2809844892c2c7310163810889002058ac382c049616024b0b04c4058204c2c00209123d10a8d87054692d2a37a215d30e0ae925854692c2b832095198aca8de88566c382b34961599880a8c65654631f2a34961571880ab862854602b2a300f951804ca8d2585486412a43101520cc4a9062854801e2a400895181008900b054004c2a001b9123d10a7462853a03622461c14a24b0a5125853062029802614a24b0a54c4052a04029401a9123d10a11870508c382904961421904a10c6a508c3828c3101420c7ca1125850e6352873101438c50a1003e50801328401a1120160a000985000402800159124940995e884cac382654a6932a5309952984f294126549613ba5009952584ca92c27231a93918809c8c984ca92c26e32093718809b8c804ca6362654a013519009a86284ca64026800913299309980224ca02a224008131b0e095d2584ae92c25f31012f813095d2584b862025c02012b80d895d2584b062025801a12b80a4891e88452c38229496914bd109458704a292c22949612799048a525849864124c31a91498ac8a4c4e45294c2474a012398848a5e88482c3824149612080f49040624826202291959148c7c8a525847663523b31011d8c508a405645201f229009914a4b08c4c6a46262023119e9188c508c403c46201222949611519048a8c4045433122a18a11500788a802245202822461c112803089925844a008224007800c94052806c442f4414a6278a5316087466843ac3f14a61c8a5494085de8842e04c21800c90bb0e052929e2952502107a210830e084069c42034a2104a68a530e083928229493714a928104bd1082587041292c14a02a103993c52863840a63f14a01e10198dc528cb040031c2003198a500c07f8c5629400c1fc3108a549407c5e883e2c381f14a68f8a5047c52583e201d1f100c8f881007c801a3e262014a4960f599047acc403d63411eb18a0f58d385292583c8f481e83268f2188079067a3c83141e41a10a530e071929a38c92c1c600e0ef98807192583b66201db18a0ed8d3071866c38c92c1d53208ea98807546283aa3341c64a60e9193074865438c92c1cd3208e6988073462839a3281c618f0e324b071cc8238e6201c718a0e38c7071867c29433714a9280dc3d106e189c37092c1b83268dc19046e0c523706201b81a60dd8cc46e06523703141b819b0a525346c52583626201b13260d98ca86c463c36233214a1958a54940689e88344c381a24a70d124d86892583526401a21a60d30cd069864a34431d1a23200d18c506886542949481a018f8a5009067a4a030cf4418661c0c3192066929a30c63c1984a08c324b0618c9c30c6491864a40c998f4619e88318c3818c4a08c624b0630c8031a62a18c31e0c318d8618c5430c32a18631e0c38c5061863c294c3816a4a68b524b05a8c402d492c17e3100bf0c505f86982d492c1793208bc98805e46282f234016a19b0b524b05ccc822e662017318a0b98cd05a92982e064c1701950b524b05acc822d662016b18a0b58ca05a863429404e14a4960b1993458cc402c633116318a0b181085286282c203614a02c0af80cc5298702b431415a01b0ad0048568054294c381544a68aa24b05506282a802a15400f0a5006c52987029694114b4960a598a852c62829602a14b0090a58068528012002f440021a48a3b10c009872004f441427a20a180a850987000525013c62089e30e04f069227804913c4a18010cf44e926e0052501334a7099bd104d9298266629133194899a4cc00a4a0258f4412c62709631084b003425800e12c4968013d10489886244c391227a209300d849987024403312200d891003c48925800525011962088cb0e046528223292c11919a08d8d244640922326430027a287f3d103f929022ac430fe61f87f30e43f9e88222c380fe4a187f313043927e1fcf4810c49b87f25304292661fc92d0fe7a208330e04192581fc9481041a187f0cd040867e1fc94810002187f00fc3f8c8200494c0fc49887ca4b03e467a1f26370027a207730e03b92861dc94c0f449987724b43b9e881e0c380f04960770ccc3b8c6a0052500e47a207231383918701c892c0e41a60738cc43900981ca0310e43158013d103598861acc390d67a206fb0e03592861ac9370d64a606da4cc35925a1acf440d761c06ba4b0358c400052500cd61c066a50433525819a6410cd31a866988033409219a3430024960649934324c4019233700292805f30e02f929a17c9410be49605f19042f869c17c3360be32605f8ca82f866600403c0bc9280563d102b189c158c490ac02605bb0e02b129c15894c0b449f05624b02b189016264d0ac32085618a42b0c401580310ac195801494026de8813694d09b4a084da4b026cc6a13634e09b7a204fb0e027cc6a13e62009f19484f8d3026d29813864009c19504d8c9c00a4a0124f4409261c049253824926c12492c09219b049009424863e00525007f7a203fb0e01fd29a0fe94107f49603f99381fcc840fe63e07f31b03f9930218c640fe62a07f02703f80d81fc0540fe04c08000703f8c54009e880a4c4305261c8293d101e40540f2c380524a182924dc1492980ea9330524968293d101c58700e292c0523218293d101b18700d892c06c32082918dc149e880cec3806749603398d4148c560a4f4406261c03124b0188c400a404305249e02f80dc1480980ba033052015829009c14803e0a463c05731802b804c1480980a804005400782900241486280049480464a0823012013925808c93c04c3208232520128c4008c3490464a40238c5011808600492c03f32681f98800fc67a07e33103f18a01f80dc00987007494d03a49601d18800e806600492c03362401b99340ccc4006633103318a01980ac00a4a003ef4401f4a680fa50407d26a03e92c01f31a80f988007c09c03ef4402361c01198d408cc4004632902318a011813007d29804202a01f00f00f809c00987003632501b18a00d807c00987002c94d01649600b0c500580260052500087a200430e002129a01094100849600418a8020c4001031e00802700400d802005401000800800780130e000cc4000633600318f001802400801000203f000 i
def s29Tags := dagTraceTags s29Mask 107 (dagTagBases s29StockWords 0x3ffffffffffffff0000000000007ffffffe0000001ffffff000000ffff0003fffc003ffe001ffc001fc01c007f807f87803c03fc7f8307f27f080c0fcf0fc740607f0f98c1b81e81fe07e0071ff20e1ff 0x3ffeb7effefefbfcc24b84e48887ea3f73c60610d1f66fec101c08a9f70923b7b5012bbe095d5c108ac01c820908534280348054690002a0070c9885060581426462050000080200061220090132221b5 107) 10 s29Data
def s29States := dagTrace s29Mask s29StockWords 10 s29Data
def s29MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s29Moves := dagMoves s29MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Autos : DagMovesOK s29Mask s29Goal 64 s29Moves := dagMovesOfCheck (by decide +kernel)
def s29Check := dagCheckNode s29Mask s29Goal s29Chart (dagKnownCloses s29Goal s29Cuts) 2411 s29States s29Moves s29Links s29Sample s29Tags
def s29RootAt (token : Nat) : Bool :=
  let s := rootState s29StockWords 10 token
  !dagAllowedRoot s29Witnesses s.2.1 || dagLocal s29Mask s29Goal s29Chart (dagKnownCloses s29Goal s29Cuts) s ||
  dagRef 2411 s29States s29Moves s29Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29RootBlock0 : treeBlock 0 64 s29RootAt = true := by decide +kernel
theorem s29Roots : dagCheckRoots s29Mask s29Goal s29Chart (dagKnownCloses s29Goal s29Cuts) s29Witnesses (dagRef 2411 s29States s29Moves s29Links 0) s29StockWords 10 = true := s29RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block0 : treeBlock 0 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block16 : treeBlock 16 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block32 : treeBlock 32 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block48 : treeBlock 48 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block64 : treeBlock 64 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block80 : treeBlock 80 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block96 : treeBlock 96 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block112 : treeBlock 112 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block128 : treeBlock 128 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block144 : treeBlock 144 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block160 : treeBlock 160 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block176 : treeBlock 176 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block192 : treeBlock 192 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block208 : treeBlock 208 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block224 : treeBlock 224 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block240 : treeBlock 240 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block256 : treeBlock 256 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block272 : treeBlock 272 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block288 : treeBlock 288 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block304 : treeBlock 304 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block320 : treeBlock 320 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block336 : treeBlock 336 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block352 : treeBlock 352 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block368 : treeBlock 368 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block384 : treeBlock 384 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block400 : treeBlock 400 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block416 : treeBlock 416 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block432 : treeBlock 432 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block448 : treeBlock 448 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block464 : treeBlock 464 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block480 : treeBlock 480 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block496 : treeBlock 496 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block512 : treeBlock 512 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block528 : treeBlock 528 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block544 : treeBlock 544 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block560 : treeBlock 560 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block576 : treeBlock 576 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block592 : treeBlock 592 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block608 : treeBlock 608 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block624 : treeBlock 624 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block640 : treeBlock 640 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block656 : treeBlock 656 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block672 : treeBlock 672 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block688 : treeBlock 688 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block704 : treeBlock 704 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block720 : treeBlock 720 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block736 : treeBlock 736 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block752 : treeBlock 752 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block768 : treeBlock 768 8 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block776 : treeBlock 776 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block792 : treeBlock 792 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block808 : treeBlock 808 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block824 : treeBlock 824 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block840 : treeBlock 840 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block856 : treeBlock 856 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block872 : treeBlock 872 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block888 : treeBlock 888 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block904 : treeBlock 904 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block920 : treeBlock 920 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block936 : treeBlock 936 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block952 : treeBlock 952 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block968 : treeBlock 968 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block984 : treeBlock 984 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1000 : treeBlock 1000 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1016 : treeBlock 1016 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1032 : treeBlock 1032 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1048 : treeBlock 1048 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1064 : treeBlock 1064 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1080 : treeBlock 1080 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1096 : treeBlock 1096 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1112 : treeBlock 1112 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1128 : treeBlock 1128 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1144 : treeBlock 1144 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1160 : treeBlock 1160 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1176 : treeBlock 1176 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1192 : treeBlock 1192 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1208 : treeBlock 1208 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1224 : treeBlock 1224 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1240 : treeBlock 1240 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1256 : treeBlock 1256 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1272 : treeBlock 1272 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1288 : treeBlock 1288 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1304 : treeBlock 1304 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1320 : treeBlock 1320 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1336 : treeBlock 1336 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1352 : treeBlock 1352 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1368 : treeBlock 1368 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1384 : treeBlock 1384 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1400 : treeBlock 1400 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1416 : treeBlock 1416 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1432 : treeBlock 1432 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1448 : treeBlock 1448 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1464 : treeBlock 1464 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1480 : treeBlock 1480 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1496 : treeBlock 1496 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1512 : treeBlock 1512 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1528 : treeBlock 1528 1 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1529 : treeBlock 1529 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1545 : treeBlock 1545 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1561 : treeBlock 1561 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1577 : treeBlock 1577 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1593 : treeBlock 1593 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1609 : treeBlock 1609 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1625 : treeBlock 1625 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1641 : treeBlock 1641 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1657 : treeBlock 1657 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1673 : treeBlock 1673 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1689 : treeBlock 1689 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1705 : treeBlock 1705 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1721 : treeBlock 1721 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1737 : treeBlock 1737 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1753 : treeBlock 1753 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1769 : treeBlock 1769 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1785 : treeBlock 1785 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1801 : treeBlock 1801 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1817 : treeBlock 1817 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1833 : treeBlock 1833 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1849 : treeBlock 1849 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1865 : treeBlock 1865 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1881 : treeBlock 1881 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1897 : treeBlock 1897 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1913 : treeBlock 1913 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1929 : treeBlock 1929 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1945 : treeBlock 1945 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1961 : treeBlock 1961 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1977 : treeBlock 1977 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block1993 : treeBlock 1993 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2009 : treeBlock 2009 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2025 : treeBlock 2025 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2041 : treeBlock 2041 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2057 : treeBlock 2057 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2073 : treeBlock 2073 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2089 : treeBlock 2089 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2105 : treeBlock 2105 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2121 : treeBlock 2121 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2137 : treeBlock 2137 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2153 : treeBlock 2153 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2169 : treeBlock 2169 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2185 : treeBlock 2185 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2201 : treeBlock 2201 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2217 : treeBlock 2217 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2233 : treeBlock 2233 3 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2236 : treeBlock 2236 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2252 : treeBlock 2252 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2268 : treeBlock 2268 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2284 : treeBlock 2284 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2300 : treeBlock 2300 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2316 : treeBlock 2316 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2332 : treeBlock 2332 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2348 : treeBlock 2348 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2364 : treeBlock 2364 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2380 : treeBlock 2380 16 s29Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Block2396 : treeBlock 2396 15 s29Check = true := by decide +kernel
theorem s29Verified : treeBlock 0 2411 s29Check = true := (@treeBlock_merge 0 1208 1203 s29Check (@treeBlock_merge 0 608 600 s29Check (@treeBlock_merge 0 304 304 s29Check (@treeBlock_merge 0 144 160 s29Check (@treeBlock_merge 0 64 80 s29Check (@treeBlock_merge 0 32 32 s29Check (@treeBlock_merge 0 16 16 s29Check s29Block0 s29Block16) (@treeBlock_merge 32 16 16 s29Check s29Block32 s29Block48)) (@treeBlock_merge 64 32 48 s29Check (@treeBlock_merge 64 16 16 s29Check s29Block64 s29Block80) (@treeBlock_merge 96 16 32 s29Check s29Block96 (@treeBlock_merge 112 16 16 s29Check s29Block112 s29Block128)))) (@treeBlock_merge 144 80 80 s29Check (@treeBlock_merge 144 32 48 s29Check (@treeBlock_merge 144 16 16 s29Check s29Block144 s29Block160) (@treeBlock_merge 176 16 32 s29Check s29Block176 (@treeBlock_merge 192 16 16 s29Check s29Block192 s29Block208))) (@treeBlock_merge 224 32 48 s29Check (@treeBlock_merge 224 16 16 s29Check s29Block224 s29Block240) (@treeBlock_merge 256 16 32 s29Check s29Block256 (@treeBlock_merge 272 16 16 s29Check s29Block272 s29Block288))))) (@treeBlock_merge 304 144 160 s29Check (@treeBlock_merge 304 64 80 s29Check (@treeBlock_merge 304 32 32 s29Check (@treeBlock_merge 304 16 16 s29Check s29Block304 s29Block320) (@treeBlock_merge 336 16 16 s29Check s29Block336 s29Block352)) (@treeBlock_merge 368 32 48 s29Check (@treeBlock_merge 368 16 16 s29Check s29Block368 s29Block384) (@treeBlock_merge 400 16 32 s29Check s29Block400 (@treeBlock_merge 416 16 16 s29Check s29Block416 s29Block432)))) (@treeBlock_merge 448 80 80 s29Check (@treeBlock_merge 448 32 48 s29Check (@treeBlock_merge 448 16 16 s29Check s29Block448 s29Block464) (@treeBlock_merge 480 16 32 s29Check s29Block480 (@treeBlock_merge 496 16 16 s29Check s29Block496 s29Block512))) (@treeBlock_merge 528 32 48 s29Check (@treeBlock_merge 528 16 16 s29Check s29Block528 s29Block544) (@treeBlock_merge 560 16 32 s29Check s29Block560 (@treeBlock_merge 576 16 16 s29Check s29Block576 s29Block592)))))) (@treeBlock_merge 608 296 304 s29Check (@treeBlock_merge 608 144 152 s29Check (@treeBlock_merge 608 64 80 s29Check (@treeBlock_merge 608 32 32 s29Check (@treeBlock_merge 608 16 16 s29Check s29Block608 s29Block624) (@treeBlock_merge 640 16 16 s29Check s29Block640 s29Block656)) (@treeBlock_merge 672 32 48 s29Check (@treeBlock_merge 672 16 16 s29Check s29Block672 s29Block688) (@treeBlock_merge 704 16 32 s29Check s29Block704 (@treeBlock_merge 720 16 16 s29Check s29Block720 s29Block736)))) (@treeBlock_merge 752 72 80 s29Check (@treeBlock_merge 752 24 48 s29Check (@treeBlock_merge 752 16 8 s29Check s29Block752 s29Block768) (@treeBlock_merge 776 16 32 s29Check s29Block776 (@treeBlock_merge 792 16 16 s29Check s29Block792 s29Block808))) (@treeBlock_merge 824 32 48 s29Check (@treeBlock_merge 824 16 16 s29Check s29Block824 s29Block840) (@treeBlock_merge 856 16 32 s29Check s29Block856 (@treeBlock_merge 872 16 16 s29Check s29Block872 s29Block888))))) (@treeBlock_merge 904 144 160 s29Check (@treeBlock_merge 904 64 80 s29Check (@treeBlock_merge 904 32 32 s29Check (@treeBlock_merge 904 16 16 s29Check s29Block904 s29Block920) (@treeBlock_merge 936 16 16 s29Check s29Block936 s29Block952)) (@treeBlock_merge 968 32 48 s29Check (@treeBlock_merge 968 16 16 s29Check s29Block968 s29Block984) (@treeBlock_merge 1000 16 32 s29Check s29Block1000 (@treeBlock_merge 1016 16 16 s29Check s29Block1016 s29Block1032)))) (@treeBlock_merge 1048 80 80 s29Check (@treeBlock_merge 1048 32 48 s29Check (@treeBlock_merge 1048 16 16 s29Check s29Block1048 s29Block1064) (@treeBlock_merge 1080 16 32 s29Check s29Block1080 (@treeBlock_merge 1096 16 16 s29Check s29Block1096 s29Block1112))) (@treeBlock_merge 1128 32 48 s29Check (@treeBlock_merge 1128 16 16 s29Check s29Block1128 s29Block1144) (@treeBlock_merge 1160 16 32 s29Check s29Block1160 (@treeBlock_merge 1176 16 16 s29Check s29Block1176 s29Block1192))))))) (@treeBlock_merge 1208 593 610 s29Check (@treeBlock_merge 1208 304 289 s29Check (@treeBlock_merge 1208 144 160 s29Check (@treeBlock_merge 1208 64 80 s29Check (@treeBlock_merge 1208 32 32 s29Check (@treeBlock_merge 1208 16 16 s29Check s29Block1208 s29Block1224) (@treeBlock_merge 1240 16 16 s29Check s29Block1240 s29Block1256)) (@treeBlock_merge 1272 32 48 s29Check (@treeBlock_merge 1272 16 16 s29Check s29Block1272 s29Block1288) (@treeBlock_merge 1304 16 32 s29Check s29Block1304 (@treeBlock_merge 1320 16 16 s29Check s29Block1320 s29Block1336)))) (@treeBlock_merge 1352 80 80 s29Check (@treeBlock_merge 1352 32 48 s29Check (@treeBlock_merge 1352 16 16 s29Check s29Block1352 s29Block1368) (@treeBlock_merge 1384 16 32 s29Check s29Block1384 (@treeBlock_merge 1400 16 16 s29Check s29Block1400 s29Block1416))) (@treeBlock_merge 1432 32 48 s29Check (@treeBlock_merge 1432 16 16 s29Check s29Block1432 s29Block1448) (@treeBlock_merge 1464 16 32 s29Check s29Block1464 (@treeBlock_merge 1480 16 16 s29Check s29Block1480 s29Block1496))))) (@treeBlock_merge 1512 129 160 s29Check (@treeBlock_merge 1512 49 80 s29Check (@treeBlock_merge 1512 17 32 s29Check (@treeBlock_merge 1512 16 1 s29Check s29Block1512 s29Block1528) (@treeBlock_merge 1529 16 16 s29Check s29Block1529 s29Block1545)) (@treeBlock_merge 1561 32 48 s29Check (@treeBlock_merge 1561 16 16 s29Check s29Block1561 s29Block1577) (@treeBlock_merge 1593 16 32 s29Check s29Block1593 (@treeBlock_merge 1609 16 16 s29Check s29Block1609 s29Block1625)))) (@treeBlock_merge 1641 80 80 s29Check (@treeBlock_merge 1641 32 48 s29Check (@treeBlock_merge 1641 16 16 s29Check s29Block1641 s29Block1657) (@treeBlock_merge 1673 16 32 s29Check s29Block1673 (@treeBlock_merge 1689 16 16 s29Check s29Block1689 s29Block1705))) (@treeBlock_merge 1721 32 48 s29Check (@treeBlock_merge 1721 16 16 s29Check s29Block1721 s29Block1737) (@treeBlock_merge 1753 16 32 s29Check s29Block1753 (@treeBlock_merge 1769 16 16 s29Check s29Block1769 s29Block1785)))))) (@treeBlock_merge 1801 304 306 s29Check (@treeBlock_merge 1801 144 160 s29Check (@treeBlock_merge 1801 64 80 s29Check (@treeBlock_merge 1801 32 32 s29Check (@treeBlock_merge 1801 16 16 s29Check s29Block1801 s29Block1817) (@treeBlock_merge 1833 16 16 s29Check s29Block1833 s29Block1849)) (@treeBlock_merge 1865 32 48 s29Check (@treeBlock_merge 1865 16 16 s29Check s29Block1865 s29Block1881) (@treeBlock_merge 1897 16 32 s29Check s29Block1897 (@treeBlock_merge 1913 16 16 s29Check s29Block1913 s29Block1929)))) (@treeBlock_merge 1945 80 80 s29Check (@treeBlock_merge 1945 32 48 s29Check (@treeBlock_merge 1945 16 16 s29Check s29Block1945 s29Block1961) (@treeBlock_merge 1977 16 32 s29Check s29Block1977 (@treeBlock_merge 1993 16 16 s29Check s29Block1993 s29Block2009))) (@treeBlock_merge 2025 32 48 s29Check (@treeBlock_merge 2025 16 16 s29Check s29Block2025 s29Block2041) (@treeBlock_merge 2057 16 32 s29Check s29Block2057 (@treeBlock_merge 2073 16 16 s29Check s29Block2073 s29Block2089))))) (@treeBlock_merge 2105 147 159 s29Check (@treeBlock_merge 2105 80 67 s29Check (@treeBlock_merge 2105 32 48 s29Check (@treeBlock_merge 2105 16 16 s29Check s29Block2105 s29Block2121) (@treeBlock_merge 2137 16 32 s29Check s29Block2137 (@treeBlock_merge 2153 16 16 s29Check s29Block2153 s29Block2169))) (@treeBlock_merge 2185 32 35 s29Check (@treeBlock_merge 2185 16 16 s29Check s29Block2185 s29Block2201) (@treeBlock_merge 2217 16 19 s29Check s29Block2217 (@treeBlock_merge 2233 3 16 s29Check s29Block2233 s29Block2236)))) (@treeBlock_merge 2252 80 79 s29Check (@treeBlock_merge 2252 32 48 s29Check (@treeBlock_merge 2252 16 16 s29Check s29Block2252 s29Block2268) (@treeBlock_merge 2284 16 32 s29Check s29Block2284 (@treeBlock_merge 2300 16 16 s29Check s29Block2300 s29Block2316))) (@treeBlock_merge 2332 32 47 s29Check (@treeBlock_merge 2332 16 16 s29Check s29Block2332 s29Block2348) (@treeBlock_merge 2364 16 31 s29Check s29Block2364 (@treeBlock_merge 2380 16 15 s29Check s29Block2380 s29Block2396))))))))
theorem s29Blocks : treeBlock 0 2411 s29Check = true := s29Verified
theorem s29Known : Known s29Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s5Stock) s4Stock) s3Stock) s2Stock) s1Stock) s0Stock) s19Stock) s18Stock) s17Stock) s16Stock) s15Stock) s14Stock) s13Stock) s12Stock) s11Stock) s10Stock) s9Stock) s8Stock) s7Stock) s6Stock) s28Stock) s27Stock) s26Stock) s25Stock) s24Stock) s22Stock) s21Stock) s23Stock) s20Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Stock : Lower s29Mask s29StockWords s29Goal 11 := by
  apply lowerDag _ _ _ _ s29Autos _ _ _ s29Known _ s29Roots s29Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s29StockWords; decide +kernel
  · decide +kernel
  · simp only [s29Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

end PEqualNP.Outside.L_meta_36220

open PEqualNP.Outside.L_meta_36220 in
theorem PEqualNP.Outside.L_meta_36220 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074664 * 2 ^ 32 + 4276812008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074664 * 2 ^ 32 + 4276812008) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro t h
  let raw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]
  let goal : BitVec 64 := 0xfeeefae8feeaf8e8
  have root : Lower (fullMask 64) (raw.map BitVec.toNat) goal.toNat 11 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s29Stock
  have size : 11 ≤ t :=
    hcsLower (n := 6) raw goal 11 _ (by decide +kernel) (by decide +kernel) root t h
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [3, 5]⟩, ⟨.and, [3, 8]⟩, ⟨.and, [1, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [0, 11]⟩, ⟨.and, [6, 12]⟩, ⟨.and, [7, 13]⟩, ⟨.or, [14, 15]⟩], 16⟩
  refine ⟨circuit, ?_, ?_, by decide +kernel⟩
  · intro gate member
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact Nat.le_trans (by decide +kernel : circuit.size ≤ 11) size

