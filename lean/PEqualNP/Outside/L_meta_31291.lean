import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_31291

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


def moveStage0 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0x5555555555555555555555555555555555555555555555555555555555555555, 1)], [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 1)])
def moveStage1 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xc3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3c3, 0), (0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c, 2)], [(0x3030303030303030303030303030303030303030303030303030303030303030, 2)])
def moveStage2 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33cc33, 0), (0xcc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc00cc, 6)], [(0x3300330033003300330033003300330033003300330033003300330033003300, 6)])
def moveStage3 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00f, 0), (0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f0, 4)], [(0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f00, 4)])
def moveStage4 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff, 16)], [(0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 16)])
def moveStage5 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffffffffffffffff00000000000000000000000000000000ffffffffffffffff, 0), (0xffffffffffffffff0000000000000000, 64)], [(0xffffffffffffffff00000000000000000000000000000000, 64)])
def moveStage6 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffffffff0000000000000000ffffffffffffffff0000000000000000ffffffff, 0), (0xffffffff000000000000000000000000ffffffff00000000, 32)], [(0xffffffff000000000000000000000000ffffffff0000000000000000, 32)])
def moveStage7 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcccccccc33333333cccccccc33333333cccccccc33333333cccccccc33333333, 0), (0xcccccccc00000000cccccccc00000000cccccccc00000000cccccccc, 30)], [(0x3333333300000000333333330000000033333333000000003333333300000000, 30)])
def moveStage8 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0ff0f0f0f00f0f0f0f, 0), (0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f0, 28)], [(0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f00000000, 28)])
def moveStage9 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ffff00ff0000ff00ff, 0), (0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00, 24)], [(0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff00000000, 24)])
def moveStage10 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffff, 0), (0xffff000000000000ffff000000000000ffff000000000000ffff0000, 16)], [(0xffff000000000000ffff000000000000ffff000000000000ffff00000000, 16)])
def moveStage11 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xaaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555aaaa5555, 0), (0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa, 15)], [(0x5555000055550000555500005555000055550000555500005555000055550000, 15)])
def moveStage12 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xcccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333cccc3333, 0), (0xcccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc0000cccc, 14)], [(0x3333000033330000333300003333000033330000333300003333000033330000, 14)])
def moveStage13 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ff, 0), (0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff00, 8)], [(0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000, 8)])
def moveStage14 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0x9999999999999999999999999999999999999999999999999999999999999999, 0), (0x2222222222222222222222222222222222222222222222222222222222222222, 1)], [(0x4444444444444444444444444444444444444444444444444444444444444444, 1)])
def moveStage15 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xaaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555aaaaaaaa55555555, 0), (0xaaaaaaaa00000000aaaaaaaa00000000aaaaaaaa00000000aaaaaaaa, 31)], [(0x5555555500000000555555550000000055555555000000005555555500000000, 31)])
def moveStage16 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xaa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55aa55, 0), (0xaa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa00aa, 7)], [(0x5500550055005500550055005500550055005500550055005500550055005500, 7)])
def moveStage17 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xf0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0ff0f00f0f, 0), (0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0, 12)], [(0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f0000, 12)])
def moveStage18 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff, 8)], [(0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 8)])
def moveStage19 : (List (Nat × Nat) × List (Nat × Nat)) := ([(0xffffffff00000000ffffffff0000000000000000ffffffff00000000ffffffff, 0), (0xffffffff00000000ffffffff00000000, 96)], [(0xffffffff00000000ffffffff00000000000000000000000000000000, 96)])
def moveStages : Array (List (Nat × Nat) × List (Nat × Nat)) := #[moveStage0, moveStage1, moveStage2, moveStage3, moveStage4, moveStage5, moveStage6, moveStage7, moveStage8, moveStage9, moveStage10, moveStage11, moveStage12, moveStage13, moveStage14, moveStage15, moveStage16, moveStage17, moveStage18, moveStage19]
def sBase : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
def sGoal : Nat := 0xfffffffffffffffffffffffffffefffcfffffffffffefffcfffefffceeeeaa00
def s0Mask : Nat := 0x5000000050000000500000005
abbrev s0Goal : Nat := sGoal &&& s0Mask
abbrev s0StockWords : List Nat := projectDAGStock s0Mask sBase [1, 5, 6]
def s0Fact : (Nat × List Nat × Nat × Nat) := (s0Mask, s0StockWords, 4, s0Goal)
def s0Cuts : List (Nat × List Nat × Nat × Nat) := []
def s0Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[34, 66, 96, 34, 34, 34, 34, 34, 34, 34, 34, 34, 2, 32, 64, 2, 2, 2, 2, 2, 2, 2, 2, 2], rfl⟩
def s0Sample : (Nat × Nat) := (0x201804060201080442100880422, 6)
def s0Witnesses := unpackWitnesses s0StockWords [33856, 311360, 573472]
def s0Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x1 0x7 2 1 3 1 1 1
def s0Data : (Nat → Nat × Nat) := fun i => decodeNode 1 4 0xe i
def s0Tags := dagTraceTags s0Mask 6 (dagTagBases s0StockWords 0x3cccf 0x28485 6) 3 s0Data
def s0States := dagTrace s0Mask s0StockWords 3 s0Data
def s0MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := []
def s0Moves := dagMoves s0MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Autos : DagMovesOK s0Mask s0Goal 256 s0Moves := dagMovesOfCheck (by decide +kernel)
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
def s1Mask : Nat := 0xa0000000a0000000a0000000a
abbrev s1Goal : Nat := sGoal &&& s1Mask
abbrev s1StockWords : List Nat := projectDAGStock s1Mask sBase [1, 5, 6]
def s1Fact : (Nat × List Nat × Nat × Nat) := (s1Mask, s1StockWords, 4, s1Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Stock : Lower s1Mask s1StockWords s1Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [0]) s0Stock (by decide +kernel)
def s2Mask : Nat := 0x11000000110000001100000011
abbrev s2Goal : Nat := sGoal &&& s2Mask
abbrev s2StockWords : List Nat := projectDAGStock s2Mask sBase [2, 5, 6]
def s2Fact : (Nat × List Nat × Nat × Nat) := (s2Mask, s2StockWords, 4, s2Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Stock : Lower s2Mask s2StockWords s2Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [1]) s0Stock (by decide +kernel)
def s3Mask : Nat := 0x101000001010000010100000101
abbrev s3Goal : Nat := sGoal &&& s3Mask
abbrev s3StockWords : List Nat := projectDAGStock s3Mask sBase [3, 5, 6]
def s3Fact : (Nat × List Nat × Nat × Nat) := (s3Mask, s3StockWords, 4, s3Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Stock : Lower s3Mask s3StockWords s3Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [2, 3]) s0Stock (by decide +kernel)
def s4Mask : Nat := 0x1010000010100000101000001010000
abbrev s4Goal : Nat := sGoal &&& s4Mask
abbrev s4StockWords : List Nat := projectDAGStock s4Mask sBase [3, 5, 6]
def s4Fact : (Nat × List Nat × Nat × Nat) := (s4Mask, s4StockWords, 4, s4Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Stock : Lower s4Mask s4StockWords s4Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [2, 3, 4]) s0Stock (by decide +kernel)
def s5Mask : Nat := 0x50000000500000000000000000000000500000005
abbrev s5Goal : Nat := sGoal &&& s5Mask
abbrev s5StockWords : List Nat := projectDAGStock s5Mask sBase [1, 5, 7]
def s5Fact : (Nat × List Nat × Nat × Nat) := (s5Mask, s5StockWords, 4, s5Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Stock : Lower s5Mask s5StockWords s5Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [5]) s0Stock (by decide +kernel)
def s6Mask : Nat := 0x5000000000000000500000000000000050000000000000005
abbrev s6Goal : Nat := sGoal &&& s6Mask
abbrev s6StockWords : List Nat := projectDAGStock s6Mask sBase [1, 6, 7]
def s6Fact : (Nat × List Nat × Nat × Nat) := (s6Mask, s6StockWords, 4, s6Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Stock : Lower s6Mask s6StockWords s6Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [6, 5]) s0Stock (by decide +kernel)
def s7Mask : Nat := 0x100000001000000010000000100000001000000010000000100000001
abbrev s7Goal : Nat := sGoal &&& s7Mask
abbrev s7StockWords : List Nat := projectDAGStock s7Mask sBase [5, 6, 7]
def s7Fact : (Nat × List Nat × Nat × Nat) := (s7Mask, s7StockWords, 4, s7Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Stock : Lower s7Mask s7StockWords s7Goal 4 := dagShiftLower (width := 256) (moveSchedule moveStages [7, 8, 9, 10, 6, 5]) s0Stock (by decide +kernel)
def s8Mask : Nat := 0x55000000550000005500000055
abbrev s8Goal : Nat := sGoal &&& s8Mask
abbrev s8StockWords : List Nat := projectDAGStock s8Mask sBase [1, 2, 5, 6]
def s8Witnesses := unpackWitnesses s8StockWords [33856, 573504, 297024, 835616]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Stock : Lower s8Mask s8StockWords s8Goal 5 := by
  apply essentialLift (witnesses := s8Witnesses) (cut := s2Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s2StockWords) (by decide +kernel)
  · exact s2Stock
  · decide +kernel
def s9Mask : Nat := 0x303000003030000030300000303
abbrev s9Goal : Nat := sGoal &&& s9Mask
abbrev s9StockWords : List Nat := projectDAGStock s9Mask sBase [0, 3, 5, 6]
def s9Fact : (Nat × List Nat × Nat × Nat) := (s9Mask, s9StockWords, 5, s9Goal)
def s9Witnesses := unpackWitnesses s9StockWords [4616, 299585, 574017, 836129]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9Stock : Lower s9Mask s9StockWords s9Goal 5 := by
  apply essentialLift (witnesses := s9Witnesses) (cut := s3Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s3StockWords) (by decide +kernel)
  · exact s3Stock
  · decide +kernel
def s10Mask : Nat := 0x505000005050000050500000505
abbrev s10Goal : Nat := sGoal &&& s10Mask
abbrev s10StockWords : List Nat := projectDAGStock s10Mask sBase [1, 3, 5, 6]
def s10Fact : (Nat × List Nat × Nat × Nat) := (s10Mask, s10StockWords, 5, s10Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Stock : Lower s10Mask s10StockWords s10Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [3]) s8Stock (by decide +kernel)
def s11Mask : Nat := 0xa0a00000a0a00000a0a00000a0a
abbrev s11Goal : Nat := sGoal &&& s11Mask
abbrev s11StockWords : List Nat := projectDAGStock s11Mask sBase [1, 3, 5, 6]
def s11Fact : (Nat × List Nat × Nat × Nat) := (s11Mask, s11StockWords, 5, s11Goal)
def s11Witnesses := unpackWitnesses s11StockWords [299585, 34369, 574017, 836129]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Stock : Lower s11Mask s11StockWords s11Goal 5 := by
  apply essentialLift (witnesses := s11Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
def s12Mask : Nat := 0x50005000500050005000500050005
abbrev s12Goal : Nat := sGoal &&& s12Mask
abbrev s12StockWords : List Nat := projectDAGStock s12Mask sBase [1, 4, 5, 6]
def s12Fact : (Nat × List Nat × Nat × Nat) := (s12Mask, s12StockWords, 5, s12Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Stock : Lower s12Mask s12StockWords s12Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [11, 12, 13]) s9Stock (by decide +kernel)
def s13Mask : Nat := 0xa000a000a000a000a000a000a000a
abbrev s13Goal : Nat := sGoal &&& s13Mask
abbrev s13StockWords : List Nat := projectDAGStock s13Mask sBase [1, 4, 5, 6]
def s13Fact : (Nat × List Nat × Nat × Nat) := (s13Mask, s13StockWords, 5, s13Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Stock : Lower s13Mask s13StockWords s13Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [13]) s11Stock (by decide +kernel)
def s14Mask : Nat := 0x330000003300000033000000330000
abbrev s14Goal : Nat := sGoal &&& s14Mask
abbrev s14StockWords : List Nat := projectDAGStock s14Mask sBase [0, 2, 5, 6]
def s14Fact : (Nat × List Nat × Nat × Nat) := (s14Mask, s14StockWords, 5, s14Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Stock : Lower s14Mask s14StockWords s14Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [14, 1, 3, 0, 4]) s11Stock (by decide +kernel)
def s15Mask : Nat := 0x550000005500000055000000550000
abbrev s15Goal : Nat := sGoal &&& s15Mask
abbrev s15StockWords : List Nat := projectDAGStock s15Mask sBase [1, 2, 5, 6]
def s15Fact : (Nat × List Nat × Nat × Nat) := (s15Mask, s15StockWords, 5, s15Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Stock : Lower s15Mask s15StockWords s15Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [1, 3, 0, 4]) s11Stock (by decide +kernel)
def s16Mask : Nat := 0x3030000030300000303000003030000
abbrev s16Goal : Nat := sGoal &&& s16Mask
abbrev s16StockWords : List Nat := projectDAGStock s16Mask sBase [0, 3, 5, 6]
def s16Fact : (Nat × List Nat × Nat × Nat) := (s16Mask, s16StockWords, 5, s16Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Stock : Lower s16Mask s16StockWords s16Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [14, 2, 0, 4]) s11Stock (by decide +kernel)
def s17Mask : Nat := 0x5050000050500000505000005050000
abbrev s17Goal : Nat := sGoal &&& s17Mask
abbrev s17StockWords : List Nat := projectDAGStock s17Mask sBase [1, 3, 5, 6]
def s17Fact : (Nat × List Nat × Nat × Nat) := (s17Mask, s17StockWords, 5, s17Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Stock : Lower s17Mask s17StockWords s17Goal 5 := dagShiftLower (width := 256) (moveSchedule moveStages [2, 0, 4]) s11Stock (by decide +kernel)
def s18Mask : Nat := 0x500000005000000050000000500000005000000050000000500000005
abbrev s18Goal : Nat := sGoal &&& s18Mask
abbrev s18StockWords : List Nat := projectDAGStock s18Mask sBase [1, 5, 6, 7]
def s18Cuts : List (Nat × List Nat × Nat × Nat) := [s0Fact, s5Fact, s6Fact, s7Fact]
def s18Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[34, 66, 96, 130, 160, 192, 34, 34, 34, 34, 34, 34, 2, 32, 64, 128, 2, 2, 2, 2, 2, 2, 2, 2], rfl⟩
def s18Sample : (Nat × Nat) := (0x4030080c04028040a0402080482201804060201080442100880422, 12)
def s18Witnesses := unpackWitnesses s18StockWords [66688, 344192, 622720, 884800]
def s18Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0xe0f4400313c06c4ac400a8664000008ce21845d4705b1001a159151504004c400484e400000000b306801 0x7a4b0b310043143865268c7498149001d3d25855880198a1931c38c5260c7890148b0113265064ca0d31b183361e03a28044b496156200462838070480813629246523407840090e0280e02038ca0831b0f31d1a06c1804848140701c120501c070599b0a32a1006c180a824960362004628824b0fb159d620366565cc7ca18a1102b1803e1404c08040000f 10 4 12 6 1 4
def s18Data : (Nat → Nat × Nat) := fun i => decodeNode 6 18 0x24b0162b064b1e620058a5c32b058d9832864cd9831f064b1562054c50162948ca5202b058d8d31d34ca0e0363407c133618ca86028240d8601c1c0a86013064b0262008c5020080403c0 i
def s18Tags := dagTraceTags s18Mask 12 (dagTagBases s18StockWords 0xfc0c3c3330cf 0xa80428112045 12) 6 s18Data
def s18States := dagTrace s18Mask s18StockWords 6 s18Data
def s18MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := []
def s18Moves := dagMoves s18MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Autos : DagMovesOK s18Mask s18Goal 256 s18Moves := dagMovesOfCheck (by decide +kernel)
def s18Check := dagCheckNode s18Mask s18Goal s18Chart (dagKnownCloses s18Goal s18Cuts) 33 s18States s18Moves s18Links s18Sample s18Tags
def s18RootAt (token : Nat) : Bool :=
  let s := rootState s18StockWords 6 token
  !dagAllowedRoot s18Witnesses s.2.1 || dagLocal s18Mask s18Goal s18Chart (dagKnownCloses s18Goal s18Cuts) s ||
  dagRef 33 s18States s18Moves s18Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18RootBlock0 : treeBlock 0 16 s18RootAt = true := by decide +kernel
theorem s18Roots : dagCheckRoots s18Mask s18Goal s18Chart (dagKnownCloses s18Goal s18Cuts) s18Witnesses (dagRef 33 s18States s18Moves s18Links 0) s18StockWords 6 = true := s18RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Block0 : treeBlock 0 16 s18Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Block16 : treeBlock 16 16 s18Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Block32 : treeBlock 32 1 s18Check = true := by decide +kernel
theorem s18Verified : treeBlock 0 33 s18Check = true := (@treeBlock_merge 0 16 17 s18Check s18Block0 (@treeBlock_merge 16 16 1 s18Check s18Block16 s18Block32))
theorem s18Blocks : treeBlock 0 33 s18Check = true := s18Verified
theorem s18Known : Known s18Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s7Stock) s6Stock) s5Stock) s0Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Stock : Lower s18Mask s18StockWords s18Goal 7 := by
  apply lowerDag _ _ _ _ s18Autos _ _ _ s18Known _ s18Roots s18Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s18StockWords; decide +kernel
  · decide +kernel
  · simp only [s18Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s19Mask : Nat := 0xa0000000a0000000a0000000a0000000a0000000a0000000a0000000a
abbrev s19Goal : Nat := sGoal &&& s19Mask
abbrev s19StockWords : List Nat := projectDAGStock s19Mask sBase [1, 5, 6, 7]
def s19Fact : (Nat × List Nat × Nat × Nat) := (s19Mask, s19StockWords, 7, s19Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Stock : Lower s19Mask s19StockWords s19Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [0]) s18Stock (by decide +kernel)
def s20Mask : Nat := 0x1100000011000000110000001100000011000000110000001100000011
abbrev s20Goal : Nat := sGoal &&& s20Mask
abbrev s20StockWords : List Nat := projectDAGStock s20Mask sBase [2, 5, 6, 7]
def s20Fact : (Nat × List Nat × Nat × Nat) := (s20Mask, s20StockWords, 7, s20Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Stock : Lower s20Mask s20StockWords s20Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [1]) s18Stock (by decide +kernel)
def s21Mask : Nat := 0x10100000101000001010000010100000101000001010000010100000101
abbrev s21Goal : Nat := sGoal &&& s21Mask
abbrev s21StockWords : List Nat := projectDAGStock s21Mask sBase [3, 5, 6, 7]
def s21Fact : (Nat × List Nat × Nat × Nat) := (s21Mask, s21StockWords, 7, s21Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Stock : Lower s21Mask s21StockWords s21Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [2, 3]) s18Stock (by decide +kernel)
def s22Mask : Nat := 0xf0f0f0f0f0f0f0f
abbrev s22Goal : Nat := sGoal &&& s22Mask
abbrev s22StockWords : List Nat := projectDAGStock s22Mask sBase [0, 1, 3, 4, 5]
def s22Fact : (Nat × List Nat × Nat × Nat) := (s22Mask, s22StockWords, 7, s22Goal)
def s22Cuts : List (Nat × List Nat × Nat × Nat) := []
def s22Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 17, 18, 34, 40, 9, 9, 9, 9, 9, 9, 9, 3, 10, 24, 33, 48, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s22Sample : (Nat × Nat) := (0x180e03038180c86031108c442230188c301a05068140b0182c0209, 12)
def s22Witnesses := unpackWitnesses s22StockWords [25136, 553008, 811553, 287792, 1077272]
def s22Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x341 0x5c38992c762033141008001f 6 3 12 1 3 3
def s22Data : (Nat → Nat × Nat) := fun i => decodeNode 2 7 0x10fc i
def s22Tags := dagTraceTags s22Mask 12 (dagTagBases s22StockWords 0xfe0f98c1f27e1e7 0xbc0f1041c02e0e3 12) 6 s22Data
def s22States := dagTrace s22Mask s22StockWords 6 s22Data
def s22Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 5, 4, 3, 6, 7] 0 i.val)
def s22Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 0, 2, 5, 4, 3, 6, 7] 0 i.val)
def s22Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [5, 0, 2, 1, 3, 4, 6, 7] 0 i.val)
def s22Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [1, 3, 2, 4, 5, 0, 6, 7] 0 i.val)
def s22Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 5, 4, 6, 7] 0 i.val)
def s22Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 1, 2, 0, 5, 4, 6, 7] 0 i.val)
def s22Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 5, 2, 0, 1, 3, 6, 7] 0 i.val)
def s22Move3Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [3, 4, 2, 5, 0, 1, 6, 7] 0 i.val)
def s22MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule moveStages [14, 9]), s22Move0Map, s22Move0Inverse), ((moveSchedule moveStages [15, 7, 9, 10]), s22Move1Map, s22Move1Inverse), ((moveSchedule moveStages [16, 10]), s22Move2Map, s22Move2Inverse), ((moveSchedule moveStages [11, 7, 13, 10]), s22Move3Map, s22Move3Inverse)]
def s22Moves := dagMoves s22MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22Autos : DagMovesOK s22Mask s22Goal 256 s22Moves := dagMovesOfCheck (by decide +kernel)
def s22Check := dagCheckNode s22Mask s22Goal s22Chart (dagKnownCloses s22Goal s22Cuts) 2 s22States s22Moves s22Links s22Sample s22Tags
def s22RootAt (token : Nat) : Bool :=
  let s := rootState s22StockWords 6 token
  !dagAllowedRoot s22Witnesses s.2.1 || dagLocal s22Mask s22Goal s22Chart (dagKnownCloses s22Goal s22Cuts) s ||
  dagRef 2 s22States s22Moves s22Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22RootBlock0 : treeBlock 0 32 s22RootAt = true := by decide +kernel
theorem s22Roots : dagCheckRoots s22Mask s22Goal s22Chart (dagKnownCloses s22Goal s22Cuts) s22Witnesses (dagRef 2 s22States s22Moves s22Links 0) s22StockWords 6 = true := s22RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22Block0 : treeBlock 0 2 s22Check = true := by decide +kernel
theorem s22Blocks : treeBlock 0 2 s22Check = true := s22Block0
theorem s22Known : Known s22Cuts := show Known [] from fun _ h => False.elim (List.not_mem_nil h)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22Stock : Lower s22Mask s22StockWords s22Goal 7 := by
  apply lowerDag _ _ _ _ s22Autos _ _ _ s22Known _ s22Roots s22Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s22StockWords; decide +kernel
  · decide +kernel
  · simp only [s22Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s23Mask : Nat := 0xf0f0f0f000000000f0f0f0f
abbrev s23Goal : Nat := sGoal &&& s23Mask
abbrev s23StockWords : List Nat := projectDAGStock s23Mask sBase [0, 1, 3, 4, 6]
def s23Fact : (Nat × List Nat × Nat × Nat) := (s23Mask, s23StockWords, 7, s23Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Stock : Lower s23Mask s23StockWords s23Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [6]) s22Stock (by decide +kernel)
def s24Mask : Nat := 0xf0f00000f0f00000f0f00000f0f
abbrev s24Goal : Nat := sGoal &&& s24Mask
abbrev s24StockWords : List Nat := projectDAGStock s24Mask sBase [0, 1, 3, 5, 6]
def s24Fact : (Nat × List Nat × Nat × Nat) := (s24Mask, s24StockWords, 7, s24Goal)
def s24Cuts : List (Nat × List Nat × Nat × Nat) := [s9Fact, s10Fact, s11Fact, s1Fact]
def s24Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 34, 40, 66, 72, 96, 9, 9, 9, 9, 9, 9, 3, 10, 33, 65, 3, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s24Sample : (Nat × Nat) := (0x826110984144a209248243050a8402810088140b0182c1009, 11)
def s24Witnesses := unpackWitnesses s24StockWords [5642, 561729, 296513, 836161, 1098273]
def s24Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0xe1 0xb870a4dcc96001f 5 2 12 2 1 2
def s24Data : (Nat → Nat × Nat) := fun i => decodeNode 2 14 0x24dd92c407c i
def s24Tags := dagTraceTags s24Mask 11 (dagTagBases s24StockWords 0x7c0c706dcb76c7 0x4c0430494936c2 11) 6 s24Data
def s24States := dagTrace s24Mask s24StockWords 6 s24Data
def s24Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s24Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s24MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule moveStages [6]), s24Move0Map, s24Move0Inverse)]
def s24Moves := dagMoves s24MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Autos : DagMovesOK s24Mask s24Goal 256 s24Moves := dagMovesOfCheck (by decide +kernel)
def s24Check := dagCheckNode s24Mask s24Goal s24Chart (dagKnownCloses s24Goal s24Cuts) 3 s24States s24Moves s24Links s24Sample s24Tags
def s24RootAt (token : Nat) : Bool :=
  let s := rootState s24StockWords 6 token
  !dagAllowedRoot s24Witnesses s.2.1 || dagLocal s24Mask s24Goal s24Chart (dagKnownCloses s24Goal s24Cuts) s ||
  dagRef 3 s24States s24Moves s24Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24RootBlock0 : treeBlock 0 32 s24RootAt = true := by decide +kernel
theorem s24Roots : dagCheckRoots s24Mask s24Goal s24Chart (dagKnownCloses s24Goal s24Cuts) s24Witnesses (dagRef 3 s24States s24Moves s24Links 0) s24StockWords 6 = true := s24RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Block0 : treeBlock 0 3 s24Check = true := by decide +kernel
theorem s24Blocks : treeBlock 0 3 s24Check = true := s24Block0
theorem s24Known : Known s24Cuts := extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s1Stock) s11Stock) s10Stock) s9Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Stock : Lower s24Mask s24StockWords s24Goal 7 := by
  apply lowerDag _ _ _ _ s24Autos _ _ _ s24Known _ s24Roots s24Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s24StockWords; decide +kernel
  · decide +kernel
  · simp only [s24Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s25Mask : Nat := 0x3333000033330000333300003333
abbrev s25Goal : Nat := sGoal &&& s25Mask
abbrev s25StockWords : List Nat := projectDAGStock s25Mask sBase [0, 2, 3, 5, 6]
def s25Fact : (Nat × List Nat × Nat × Nat) := (s25Mask, s25StockWords, 7, s25Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Stock : Lower s25Mask s25StockWords s25Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [1]) s24Stock (by decide +kernel)
def s26Mask : Nat := 0xf000f000f000f000f000f000f000f
abbrev s26Goal : Nat := sGoal &&& s26Mask
abbrev s26StockWords : List Nat := projectDAGStock s26Mask sBase [0, 1, 4, 5, 6]
def s26Fact : (Nat × List Nat × Nat × Nat) := (s26Mask, s26StockWords, 7, s26Goal)
def s26Cuts : List (Nat × List Nat × Nat × Nat) := [s12Fact, s13Fact, s1Fact]
def s26Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[17, 18, 34, 66, 96, 17, 17, 17, 17, 17, 17, 17, 3, 33, 48, 65, 80, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s26Sample : (Nat × Nat) := (0x281c0607020984a0522814482512090c0643180c86031108c40623010480211, 14)
def s26Witnesses := unpackWitnesses s26StockWords [41552, 565825, 304208, 843856, 1105968]
def s26Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0xe1 0xd870a4b098a001f 5 2 12 2 1 2
def s26Data : (Nat → Nat × Nat) := fun i => decodeNode 2 14 0x24b1314407c i
def s26Tags := dagTraceTags s26Mask 14 (dagTagBases s26StockWords 0x3fc0e0f373b1398bdd 0x2f8040e363001189cd 14) 6 s26Data
def s26States := dagTrace s26Mask s26StockWords 6 s26Data
def s26Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s26Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s26MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule moveStages [6]), s26Move0Map, s26Move0Inverse)]
def s26Moves := dagMoves s26MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Autos : DagMovesOK s26Mask s26Goal 256 s26Moves := dagMovesOfCheck (by decide +kernel)
def s26Check := dagCheckNode s26Mask s26Goal s26Chart (dagKnownCloses s26Goal s26Cuts) 3 s26States s26Moves s26Links s26Sample s26Tags
def s26RootAt (token : Nat) : Bool :=
  let s := rootState s26StockWords 6 token
  !dagAllowedRoot s26Witnesses s.2.1 || dagLocal s26Mask s26Goal s26Chart (dagKnownCloses s26Goal s26Cuts) s ||
  dagRef 3 s26States s26Moves s26Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26RootBlock0 : treeBlock 0 32 s26RootAt = true := by decide +kernel
theorem s26Roots : dagCheckRoots s26Mask s26Goal s26Chart (dagKnownCloses s26Goal s26Cuts) s26Witnesses (dagRef 3 s26States s26Moves s26Links 0) s26StockWords 6 = true := s26RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Block0 : treeBlock 0 3 s26Check = true := by decide +kernel
theorem s26Blocks : treeBlock 0 3 s26Check = true := s26Block0
theorem s26Known : Known s26Cuts := extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s1Stock) s13Stock) s12Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Stock : Lower s26Mask s26StockWords s26Goal 7 := by
  apply lowerDag _ _ _ _ s26Autos _ _ _ s26Known _ s26Roots s26Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s26StockWords; decide +kernel
  · decide +kernel
  · simp only [s26Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl <;> decide +kernel
def s27Mask : Nat := 0x330033003300330033003300330033
abbrev s27Goal : Nat := sGoal &&& s27Mask
abbrev s27StockWords : List Nat := projectDAGStock s27Mask sBase [0, 2, 4, 5, 6]
def s27Witnesses := unpackWitnesses s27StockWords [41552, 565825, 305232, 843856, 1105968]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Stock : Lower s27Mask s27StockWords s27Goal 6 := by
  apply essentialLift (witnesses := s27Witnesses) (cut := s14Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s14StockWords) (by decide +kernel)
  · exact s14Stock
  · decide +kernel
def s28Mask : Nat := 0x550055005500550055005500550055
abbrev s28Goal : Nat := sGoal &&& s28Mask
abbrev s28StockWords : List Nat := projectDAGStock s28Mask sBase [1, 2, 4, 5, 6]
def s28Fact : (Nat × List Nat × Nat × Nat) := (s28Mask, s28StockWords, 7, s28Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Stock : Lower s28Mask s28StockWords s28Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [11, 1, 17, 13]) s24Stock (by decide +kernel)
def s29Mask : Nat := 0xff000000ff000000ff000000ff0000
abbrev s29Goal : Nat := sGoal &&& s29Mask
abbrev s29StockWords : List Nat := projectDAGStock s29Mask sBase [0, 1, 2, 5, 6]
def s29Witnesses := unpackWitnesses s29StockWords [41552, 304208, 567376, 843856, 1105968]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Stock : Lower s29Mask s29StockWords s29Goal 6 := by
  apply essentialLift (witnesses := s29Witnesses) (cut := s15Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s15StockWords) (by decide +kernel)
  · exact s15Stock
  · decide +kernel
def s30Mask : Nat := 0x3030303030303030303030303030303
abbrev s30Goal : Nat := sGoal &&& s30Mask
abbrev s30StockWords : List Nat := projectDAGStock s30Mask sBase [0, 3, 4, 5, 6]
def s30Fact : (Nat × List Nat × Nat × Nat) := (s30Mask, s30StockWords, 7, s30Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s30Stock : Lower s30Mask s30StockWords s30Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [11, 2, 3]) s26Stock (by decide +kernel)
def s31Mask : Nat := 0x5050505050505050505050505050505
abbrev s31Goal : Nat := sGoal &&& s31Mask
abbrev s31StockWords : List Nat := projectDAGStock s31Mask sBase [1, 3, 4, 5, 6]
def s31Fact : (Nat × List Nat × Nat × Nat) := (s31Mask, s31StockWords, 7, s31Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Stock : Lower s31Mask s31StockWords s31Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [11, 2, 17]) s24Stock (by decide +kernel)
def s32Mask : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
abbrev s32Goal : Nat := sGoal &&& s32Mask
abbrev s32StockWords : List Nat := projectDAGStock s32Mask sBase [1, 3, 4, 5, 6]
def s32Fact : (Nat × List Nat × Nat × Nat) := (s32Mask, s32StockWords, 6, s32Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Stock : Lower s32Mask s32StockWords s32Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [16, 12, 17, 18, 4]) s29Stock (by decide +kernel)
def s33Mask : Nat := 0xf0f00000f0f00000f0f00000f0f0000
abbrev s33Goal : Nat := sGoal &&& s33Mask
abbrev s33StockWords : List Nat := projectDAGStock s33Mask sBase [0, 1, 3, 5, 6]
def s33Fact : (Nat × List Nat × Nat × Nat) := (s33Mask, s33StockWords, 6, s33Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s33Stock : Lower s33Mask s33StockWords s33Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [3]) s29Stock (by decide +kernel)
def s34Mask : Nat := 0xf0f00000f0f000000000000000000000f0f00000f0f
abbrev s34Goal : Nat := sGoal &&& s34Mask
abbrev s34StockWords : List Nat := projectDAGStock s34Mask sBase [0, 1, 3, 5, 7]
def s34Fact : (Nat × List Nat × Nat × Nat) := (s34Mask, s34StockWords, 7, s34Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Stock : Lower s34Mask s34StockWords s34Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [5]) s24Stock (by decide +kernel)
def s35Mask : Nat := 0xf000f000f000f0000000000000000000f000f000f000f
abbrev s35Goal : Nat := sGoal &&& s35Mask
abbrev s35StockWords : List Nat := projectDAGStock s35Mask sBase [0, 1, 4, 5, 7]
def s35Fact : (Nat × List Nat × Nat × Nat) := (s35Mask, s35StockWords, 7, s35Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Stock : Lower s35Mask s35StockWords s35Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [5]) s26Stock (by decide +kernel)
def s36Mask : Nat := 0xf0f0000000000000f0f0000000000000f0f0000000000000f0f
abbrev s36Goal : Nat := sGoal &&& s36Mask
abbrev s36StockWords : List Nat := projectDAGStock s36Mask sBase [0, 1, 3, 6, 7]
def s36Fact : (Nat × List Nat × Nat × Nat) := (s36Mask, s36StockWords, 7, s36Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Stock : Lower s36Mask s36StockWords s36Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [6, 5]) s24Stock (by decide +kernel)
def s37Mask : Nat := 0xf000f00000000000f000f00000000000f000f00000000000f000f
abbrev s37Goal : Nat := sGoal &&& s37Mask
abbrev s37StockWords : List Nat := projectDAGStock s37Mask sBase [0, 1, 4, 6, 7]
def s37Fact : (Nat × List Nat × Nat × Nat) := (s37Mask, s37StockWords, 7, s37Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Stock : Lower s37Mask s37StockWords s37Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [6, 5]) s26Stock (by decide +kernel)
def s38Mask : Nat := 0x330033000000000033003300000000003300330000000000330033
abbrev s38Goal : Nat := sGoal &&& s38Mask
abbrev s38StockWords : List Nat := projectDAGStock s38Mask sBase [0, 2, 4, 6, 7]
def s38Fact : (Nat × List Nat × Nat × Nat) := (s38Mask, s38StockWords, 6, s38Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Stock : Lower s38Mask s38StockWords s38Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [6, 5]) s27Stock (by decide +kernel)
def s39Mask : Nat := 0x3030303000000000303030300000000030303030000000003030303
abbrev s39Goal : Nat := sGoal &&& s39Mask
abbrev s39StockWords : List Nat := projectDAGStock s39Mask sBase [0, 3, 4, 6, 7]
def s39Fact : (Nat × List Nat × Nat × Nat) := (s39Mask, s39StockWords, 7, s39Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Stock : Lower s39Mask s39StockWords s39Goal 7 := dagShiftLower (width := 256) (moveSchedule moveStages [11, 2, 3, 6, 5]) s26Stock (by decide +kernel)
def s40Mask : Nat := 0x5500000055000000550000005500000055000000550000005500000055
abbrev s40Goal : Nat := sGoal &&& s40Mask
abbrev s40StockWords : List Nat := projectDAGStock s40Mask sBase [1, 2, 5, 6, 7]
def s40Witnesses := unpackWitnesses s40StockWords [66688, 606336, 329856, 884864, 1146944]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Stock : Lower s40Mask s40StockWords s40Goal 8 := by
  apply essentialLift (witnesses := s40Witnesses) (cut := s20Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s20StockWords) (by decide +kernel)
  · exact s20Stock
  · decide +kernel
def s41Mask : Nat := 0x30300000303000003030000030300000303000003030000030300000303
abbrev s41Goal : Nat := sGoal &&& s41Mask
abbrev s41StockWords : List Nat := projectDAGStock s41Mask sBase [0, 3, 5, 6, 7]
def s41Fact : (Nat × List Nat × Nat × Nat) := (s41Mask, s41StockWords, 8, s41Goal)
def s41Witnesses := unpackWitnesses s41StockWords [4616, 332417, 606849, 885377, 1147457]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Stock : Lower s41Mask s41StockWords s41Goal 8 := by
  apply essentialLift (witnesses := s41Witnesses) (cut := s21Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s21StockWords) (by decide +kernel)
  · exact s21Stock
  · decide +kernel
def s42Mask : Nat := 0x50500000505000005050000050500000505000005050000050500000505
abbrev s42Goal : Nat := sGoal &&& s42Mask
abbrev s42StockWords : List Nat := projectDAGStock s42Mask sBase [1, 3, 5, 6, 7]
def s42Fact : (Nat × List Nat × Nat × Nat) := (s42Mask, s42StockWords, 8, s42Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s42Stock : Lower s42Mask s42StockWords s42Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [3]) s40Stock (by decide +kernel)
def s43Mask : Nat := 0xa0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a00000a0a
abbrev s43Goal : Nat := sGoal &&& s43Mask
abbrev s43StockWords : List Nat := projectDAGStock s43Mask sBase [1, 3, 5, 6, 7]
def s43Fact : (Nat × List Nat × Nat × Nat) := (s43Mask, s43StockWords, 8, s43Goal)
def s43Witnesses := unpackWitnesses s43StockWords [332417, 67201, 606849, 885377, 1147457]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Stock : Lower s43Mask s43StockWords s43Goal 8 := by
  apply essentialLift (witnesses := s43Witnesses) (cut := s19Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s19StockWords) (by decide +kernel)
  · exact s19Stock
  · decide +kernel
def s44Mask : Nat := 0x111100001111000011110000111100001111000011110000111100001111
abbrev s44Goal : Nat := sGoal &&& s44Mask
abbrev s44StockWords : List Nat := projectDAGStock s44Mask sBase [2, 3, 5, 6, 7]
def s44Fact : (Nat × List Nat × Nat × Nat) := (s44Mask, s44StockWords, 8, s44Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Stock : Lower s44Mask s44StockWords s44Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [1, 3]) s40Stock (by decide +kernel)
def s45Mask : Nat := 0x222200002222000022220000222200002222000022220000222200002222
abbrev s45Goal : Nat := sGoal &&& s45Mask
abbrev s45StockWords : List Nat := projectDAGStock s45Mask sBase [2, 3, 5, 6, 7]
def s45Fact : (Nat × List Nat × Nat × Nat) := (s45Mask, s45StockWords, 8, s45Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s45Stock : Lower s45Mask s45StockWords s45Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [1]) s43Stock (by decide +kernel)
def s46Mask : Nat := 0x3000300030003000300030003000300030003000300030003000300030003
abbrev s46Goal : Nat := sGoal &&& s46Mask
abbrev s46StockWords : List Nat := projectDAGStock s46Mask sBase [0, 4, 5, 6, 7]
def s46Fact : (Nat × List Nat × Nat × Nat) := (s46Mask, s46StockWords, 6, s46Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Stock : Lower s46Mask s46StockWords s46Goal 6 := dagShiftLower (width := 256) (moveSchedule moveStages [8, 9, 6, 5]) s27Stock (by decide +kernel)
def s47Mask : Nat := 0x5000500050005000500050005000500050005000500050005000500050005
abbrev s47Goal : Nat := sGoal &&& s47Mask
abbrev s47StockWords : List Nat := projectDAGStock s47Mask sBase [1, 4, 5, 6, 7]
def s47Fact : (Nat × List Nat × Nat × Nat) := (s47Mask, s47StockWords, 8, s47Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Stock : Lower s47Mask s47StockWords s47Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [11, 12, 13]) s41Stock (by decide +kernel)
def s48Mask : Nat := 0xa000a000a000a000a000a000a000a000a000a000a000a000a000a000a000a
abbrev s48Goal : Nat := sGoal &&& s48Mask
abbrev s48StockWords : List Nat := projectDAGStock s48Mask sBase [1, 4, 5, 6, 7]
def s48Fact : (Nat × List Nat × Nat × Nat) := (s48Mask, s48StockWords, 8, s48Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48Stock : Lower s48Mask s48StockWords s48Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [13]) s43Stock (by decide +kernel)
def s49Mask : Nat := 0x33000000330000003300000033000000330000003300000033000000330000
abbrev s49Goal : Nat := sGoal &&& s49Mask
abbrev s49StockWords : List Nat := projectDAGStock s49Mask sBase [0, 2, 5, 6, 7]
def s49Fact : (Nat × List Nat × Nat × Nat) := (s49Mask, s49StockWords, 8, s49Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Stock : Lower s49Mask s49StockWords s49Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [14, 1, 3, 0, 4]) s43Stock (by decide +kernel)
def s50Mask : Nat := 0x55000000550000005500000055000000550000005500000055000000550000
abbrev s50Goal : Nat := sGoal &&& s50Mask
abbrev s50StockWords : List Nat := projectDAGStock s50Mask sBase [1, 2, 5, 6, 7]
def s50Fact : (Nat × List Nat × Nat × Nat) := (s50Mask, s50StockWords, 8, s50Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Stock : Lower s50Mask s50StockWords s50Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [1, 3, 0, 4]) s43Stock (by decide +kernel)
def s51Mask : Nat := 0x1111000011110000111100001111000011110000111100001111000011110000
abbrev s51Goal : Nat := sGoal &&& s51Mask
abbrev s51StockWords : List Nat := projectDAGStock s51Mask sBase [2, 3, 5, 6, 7]
def s51Fact : (Nat × List Nat × Nat × Nat) := (s51Mask, s51StockWords, 8, s51Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Stock : Lower s51Mask s51StockWords s51Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [1, 3, 4]) s40Stock (by decide +kernel)
def s52Mask : Nat := 0xffffffffffffffff
abbrev s52Goal : Nat := sGoal &&& s52Mask
abbrev s52StockWords : List Nat := projectDAGStock s52Mask sBase [0, 1, 2, 3, 4, 5]
def s52Fact : (Nat × List Nat × Nat × Nat) := (s52Mask, s52StockWords, 8, s52Goal)
def s52Witnesses := unpackWitnesses s52StockWords [25136, 815152, 1073697, 287792, 1341468, 550960]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s52Stock : Lower s52Mask s52StockWords s52Goal 8 := by
  apply essentialLift (witnesses := s52Witnesses) (cut := s22Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s22StockWords) (by decide +kernel)
  · exact s22Stock
  · decide +kernel
def s53Mask : Nat := 0xffffffff00000000ffffffff
abbrev s53Goal : Nat := sGoal &&& s53Mask
abbrev s53StockWords : List Nat := projectDAGStock s53Mask sBase [0, 1, 2, 3, 4, 6]
def s53Fact : (Nat × List Nat × Nat × Nat) := (s53Mask, s53StockWords, 8, s53Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Stock : Lower s53Mask s53StockWords s53Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [6]) s52Stock (by decide +kernel)
def s54Mask : Nat := 0xffff0000ffff0000ffff0000ffff
abbrev s54Goal : Nat := sGoal &&& s54Mask
abbrev s54StockWords : List Nat := projectDAGStock s54Mask sBase [0, 1, 2, 3, 5, 6]
def s54Witnesses := unpackWitnesses s54StockWords [7694, 823873, 296513, 1098305, 559681, 1360417]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Stock : Lower s54Mask s54StockWords s54Goal 8 := by
  apply essentialLift (witnesses := s54Witnesses) (cut := s25Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s25StockWords) (by decide +kernel)
  · exact s25Stock
  · decide +kernel
def s55Mask : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
abbrev s55Goal : Nat := sGoal &&& s55Mask
abbrev s55StockWords : List Nat := projectDAGStock s55Mask sBase [0, 1, 2, 4, 5, 6]
def s55Witnesses := unpackWitnesses s55StockWords [41552, 827969, 304208, 1106000, 567376, 1368112]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Stock : Lower s55Mask s55StockWords s55Goal 8 := by
  apply essentialLift (witnesses := s55Witnesses) (cut := s28Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s28StockWords) (by decide +kernel)
  · exact s28Stock
  · decide +kernel
def s56Mask : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev s56Goal : Nat := sGoal &&& s56Mask
abbrev s56StockWords : List Nat := projectDAGStock s56Mask sBase [0, 1, 3, 4, 5, 6]
def s56Fact : (Nat × List Nat × Nat × Nat) := (s56Mask, s56StockWords, 10, s56Goal)
def s56Cuts : List (Nat × List Nat × Nat × Nat) := [s22Fact, s23Fact, s24Fact, s26Fact, s30Fact, s31Fact, s32Fact, s33Fact, s11Fact, s13Fact, s16Fact, s17Fact, s1Fact, s4Fact]
def s56Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 17, 18, 34, 40, 66, 72, 96, 9, 9, 9, 9, 3, 10, 24, 33, 48, 65, 80, 3, 3, 3, 3, 3], rfl⟩
def s56Sample : (Nat × Nat) := (0xa070181c0826110984826028160305828148a0512094482492092080480512082430190c8242201080442180e03038180c86031108c4142a108a414281088c06230508804220c068141a0c06406132804860120c04806120104802110502c060b018240209, 45)
def s56Witnesses := unpackWitnesses s56StockWords [41552, 569424, 827969, 304208, 1106000, 1368112]
def s56Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0xe8d70230bc0000000003004000be15550000000000000252c000000462000000084437580000006a2000198800000030180000005a30000000a48000271000000048300000000000002118b2c06a001 0x612508e496559937a4c835263591315d01880ac69ad23412919a900c50440261c0088d7a24fb0e07d2581a6202e7a26cb10e31871d89439049bcf24b1b0c8728637253158f1881646862c33714195880c7c3062850340284a0164940ade9c54f442962744a4b090c833a620271a7110c7818010cb250257a242b0e19129c489422349671193a88c84c434e221a10280207de8910c381c49602188171e8838c388349601988179e8840c431e61c43a4b174c863a6371b3102c0d0c6066e2631f0218a0cc94060628ad250167a22a494051e88263145092808bd3c41e881af440b61c0424b010c4096f440b61c243d102187006620447a20230e00cc4098f440e6218630e029258926430931b839881186860c3370518f810c51b5e885ec432d61c6ba50e5d26f0292ce6321d318de3cc5734620661a1930cde486564231f1a18a2b810c5c06e2a02b1200f87804c040100003f 13 5 13 6 2 5
def s56Data : (Nat → Nat × Nat) := fun i => decodeNode 6 19 0x4943062182f44b98700c94277a74ef449d89d3a50281a74e33705e891250a2496443428863e0b10db7a23ec386cc6edb0e1c31036314064a0c0c51801b82f44580560bd11318a2601f05e9e83d11000982c4309e886b0e0261c1692c08c6e130e08310043370863e130e033100631408010080fc0 i
def s56Tags := dagTraceTags s56Mask 45 (dagTagBases s56StockWords 0x3ffff8000001f0003ffc000c7c01f01ff8031e0c70e03c040f927efd861c606b0c1f 0x2b7eb0000400a0002ea0100c7801e015c001020452e220001482ba8dc70e702b0457 45) 9 s56Data
def s56States := dagTrace s56Mask s56StockWords 9 s56Data
def s56Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s56Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s56Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 5, 6, 7] 0 i.val)
def s56Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 5, 6, 7] 0 i.val)
def s56Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 6, 5, 7] 0 i.val)
def s56Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 6, 5, 7] 0 i.val)
def s56MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule moveStages [6]), s56Move0Map, s56Move0Inverse), ((moveSchedule moveStages [11, 2]), s56Move1Map, s56Move1Inverse), ((moveSchedule moveStages [11, 2, 6]), s56Move2Map, s56Move2Inverse)]
def s56Moves := dagMoves s56MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Autos : DagMovesOK s56Mask s56Goal 256 s56Moves := dagMovesOfCheck (by decide +kernel)
def s56Check := dagCheckNode s56Mask s56Goal s56Chart (dagKnownCloses s56Goal s56Cuts) 49 s56States s56Moves s56Links s56Sample s56Tags
def s56RootAt (token : Nat) : Bool :=
  let s := rootState s56StockWords 9 token
  !dagAllowedRoot s56Witnesses s.2.1 || dagLocal s56Mask s56Goal s56Chart (dagKnownCloses s56Goal s56Cuts) s ||
  dagRef 49 s56States s56Moves s56Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56RootBlock0 : treeBlock 0 64 s56RootAt = true := by decide +kernel
theorem s56Roots : dagCheckRoots s56Mask s56Goal s56Chart (dagKnownCloses s56Goal s56Cuts) s56Witnesses (dagRef 49 s56States s56Moves s56Links 0) s56StockWords 9 = true := s56RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Block0 : treeBlock 0 16 s56Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Block16 : treeBlock 16 16 s56Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Block32 : treeBlock 32 16 s56Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Block48 : treeBlock 48 1 s56Check = true := by decide +kernel
theorem s56Verified : treeBlock 0 49 s56Check = true := (@treeBlock_merge 0 32 17 s56Check (@treeBlock_merge 0 16 16 s56Check s56Block0 s56Block16) (@treeBlock_merge 32 16 1 s56Check s56Block32 s56Block48))
theorem s56Blocks : treeBlock 0 49 s56Check = true := s56Verified
theorem s56Known : Known s56Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s4Stock) s1Stock) s17Stock) s16Stock) s13Stock) s11Stock) s33Stock) s32Stock) s31Stock) s30Stock) s26Stock) s24Stock) s23Stock) s22Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Stock : Lower s56Mask s56StockWords s56Goal 10 := by
  apply lowerDag _ _ _ _ s56Autos _ _ _ s56Known _ s56Roots s56Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s56StockWords; decide +kernel
  · decide +kernel
  · simp only [s56Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s57Mask : Nat := 0xffffffff000000000000000000000000ffffffff
abbrev s57Goal : Nat := sGoal &&& s57Mask
abbrev s57StockWords : List Nat := projectDAGStock s57Mask sBase [0, 1, 2, 3, 4, 7]
def s57Fact : (Nat × List Nat × Nat × Nat) := (s57Mask, s57StockWords, 8, s57Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s57Stock : Lower s57Mask s57StockWords s57Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [19, 5]) s52Stock (by decide +kernel)
def s58Mask : Nat := 0xff00ff00ff00ff000000000000000000ff00ff00ff00ff
abbrev s58Goal : Nat := sGoal &&& s58Mask
abbrev s58StockWords : List Nat := projectDAGStock s58Mask sBase [0, 1, 2, 4, 5, 7]
def s58Fact : (Nat × List Nat × Nat × Nat) := (s58Mask, s58StockWords, 8, s58Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Stock : Lower s58Mask s58StockWords s58Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [5]) s55Stock (by decide +kernel)
def s59Mask : Nat := 0xf0f0f0f0f0f0f0f00000000000000000f0f0f0f0f0f0f0f
abbrev s59Goal : Nat := sGoal &&& s59Mask
abbrev s59StockWords : List Nat := projectDAGStock s59Mask sBase [0, 1, 3, 4, 5, 7]
def s59Fact : (Nat × List Nat × Nat × Nat) := (s59Mask, s59StockWords, 10, s59Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s59Stock : Lower s59Mask s59StockWords s59Goal 10 := dagShiftLower (width := 256) (moveSchedule moveStages [5]) s56Stock (by decide +kernel)
def s60Mask : Nat := 0x333333333333333300000000000000003333333333333333
abbrev s60Goal : Nat := sGoal &&& s60Mask
abbrev s60StockWords : List Nat := projectDAGStock s60Mask sBase [0, 2, 3, 4, 5, 7]
def s60Fact : (Nat × List Nat × Nat × Nat) := (s60Mask, s60StockWords, 8, s60Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Stock : Lower s60Mask s60StockWords s60Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [11, 2, 5]) s55Stock (by decide +kernel)
def s61Mask : Nat := 0xff00ff0000000000ff00ff0000000000ff00ff0000000000ff00ff
abbrev s61Goal : Nat := sGoal &&& s61Mask
abbrev s61StockWords : List Nat := projectDAGStock s61Mask sBase [0, 1, 2, 4, 6, 7]
def s61Fact : (Nat × List Nat × Nat × Nat) := (s61Mask, s61StockWords, 8, s61Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s61Stock : Lower s61Mask s61StockWords s61Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [6, 5]) s55Stock (by decide +kernel)
def s62Mask : Nat := 0xf0f0f0f000000000f0f0f0f000000000f0f0f0f000000000f0f0f0f
abbrev s62Goal : Nat := sGoal &&& s62Mask
abbrev s62StockWords : List Nat := projectDAGStock s62Mask sBase [0, 1, 3, 4, 6, 7]
def s62Fact : (Nat × List Nat × Nat × Nat) := (s62Mask, s62StockWords, 10, s62Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s62Stock : Lower s62Mask s62StockWords s62Goal 10 := dagShiftLower (width := 256) (moveSchedule moveStages [6, 5]) s56Stock (by decide +kernel)
def s63Mask : Nat := 0x33333333000000003333333300000000333333330000000033333333
abbrev s63Goal : Nat := sGoal &&& s63Mask
abbrev s63StockWords : List Nat := projectDAGStock s63Mask sBase [0, 2, 3, 4, 6, 7]
def s63Fact : (Nat × List Nat × Nat × Nat) := (s63Mask, s63StockWords, 8, s63Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Stock : Lower s63Mask s63StockWords s63Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [11, 2, 6, 5]) s55Stock (by decide +kernel)
def s64Mask : Nat := 0x55555555000000005555555500000000555555550000000055555555
abbrev s64Goal : Nat := sGoal &&& s64Mask
abbrev s64StockWords : List Nat := projectDAGStock s64Mask sBase [1, 2, 3, 4, 6, 7]
def s64Fact : (Nat × List Nat × Nat × Nat) := (s64Mask, s64StockWords, 8, s64Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Stock : Lower s64Mask s64StockWords s64Goal 8 := dagShiftLower (width := 256) (moveSchedule moveStages [11, 1, 3, 6, 5]) s54Stock (by decide +kernel)
def s65Mask : Nat := 0xf0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f00000f0f
abbrev s65Goal : Nat := sGoal &&& s65Mask
abbrev s65StockWords : List Nat := projectDAGStock s65Mask sBase [0, 1, 3, 5, 6, 7]
def s65Fact : (Nat × List Nat × Nat × Nat) := (s65Mask, s65StockWords, 10, s65Goal)
def s65Cuts : List (Nat × List Nat × Nat × Nat) := [s41Fact, s42Fact, s43Fact, s19Fact, s24Fact, s34Fact, s36Fact]
def s65Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 34, 40, 66, 72, 96, 130, 136, 160, 192, 9, 9, 3, 10, 33, 65, 129, 3, 3, 3, 3, 3, 3, 3], rfl⟩
def s65Sample : (Nat × Nat) := (0x40b0482c140a8442a140a8042a005229028940a0c04822098442612018040600512882492090c0442050a8402810088140b0182c1009, 24)
def s65Witnesses := unpackWitnesses s65StockWords [5642, 594561, 329345, 868993, 1147521, 1409601]
def s65Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x895e0000513b0e01 0xe9406925014f4f12f4e10f444cc4e0c94e06f4424f4408c4304c3862f448ac4342c382a9430a9370292c0003f 8 3 13 4 3 3
def s65Data : (Nat → Nat × Nat) := fun i => decodeNode 4 16 0xf4f6f4e6f446940794e69371c432f443c38292c103f0 i
def s65Tags := dagTraceTags s65Mask 24 (dagTagBases s65StockWords 0xffc000c03fc03c3c3803033702c2eef1b187 0xa98000402980141418020225024266fdb182 24) 9 s65Data
def s65States := dagTrace s65Mask s65StockWords 9 s65Data
def s65Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 5, 7, 6] 0 i.val)
def s65Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 5, 7, 6] 0 i.val)
def s65Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s65Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s65Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 5, 6] 0 i.val)
def s65Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 7, 5] 0 i.val)
def s65Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 7, 5] 0 i.val)
def s65Move3Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 5, 6] 0 i.val)
def s65MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule moveStages [5]), s65Move0Map, s65Move0Inverse), ((moveSchedule moveStages [6]), s65Move1Map, s65Move1Inverse), ((moveSchedule moveStages [19, 5]), s65Move2Map, s65Move2Inverse), ((moveSchedule moveStages [6, 5]), s65Move3Map, s65Move3Inverse)]
def s65Moves := dagMoves s65MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65Autos : DagMovesOK s65Mask s65Goal 256 s65Moves := dagMovesOfCheck (by decide +kernel)
def s65Check := dagCheckNode s65Mask s65Goal s65Chart (dagKnownCloses s65Goal s65Cuts) 11 s65States s65Moves s65Links s65Sample s65Tags
def s65RootAt (token : Nat) : Bool :=
  let s := rootState s65StockWords 9 token
  !dagAllowedRoot s65Witnesses s.2.1 || dagLocal s65Mask s65Goal s65Chart (dagKnownCloses s65Goal s65Cuts) s ||
  dagRef 11 s65States s65Moves s65Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65RootBlock0 : treeBlock 0 64 s65RootAt = true := by decide +kernel
theorem s65Roots : dagCheckRoots s65Mask s65Goal s65Chart (dagKnownCloses s65Goal s65Cuts) s65Witnesses (dagRef 11 s65States s65Moves s65Links 0) s65StockWords 9 = true := s65RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65Block0 : treeBlock 0 11 s65Check = true := by decide +kernel
theorem s65Blocks : treeBlock 0 11 s65Check = true := s65Block0
theorem s65Known : Known s65Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s36Stock) s34Stock) s24Stock) s19Stock) s43Stock) s42Stock) s41Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65Stock : Lower s65Mask s65StockWords s65Goal 10 := by
  apply lowerDag _ _ _ _ s65Autos _ _ _ s65Known _ s65Roots s65Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s65StockWords; decide +kernel
  · decide +kernel
  · simp only [s65Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s66Mask : Nat := 0x333300003333000033330000333300003333000033330000333300003333
abbrev s66Goal : Nat := sGoal &&& s66Mask
abbrev s66StockWords : List Nat := projectDAGStock s66Mask sBase [0, 2, 3, 5, 6, 7]
def s66Fact : (Nat × List Nat × Nat × Nat) := (s66Mask, s66StockWords, 10, s66Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66Stock : Lower s66Mask s66StockWords s66Goal 10 := dagShiftLower (width := 256) (moveSchedule moveStages [1]) s65Stock (by decide +kernel)
def s67Mask : Nat := 0x555500005555000055550000555500005555000055550000555500005555
abbrev s67Goal : Nat := sGoal &&& s67Mask
abbrev s67StockWords : List Nat := projectDAGStock s67Mask sBase [1, 2, 3, 5, 6, 7]
def s67Fact : (Nat × List Nat × Nat × Nat) := (s67Mask, s67StockWords, 9, s67Goal)
def s67Witnesses := unpackWitnesses s67StockWords [66688, 868480, 329856, 594048, 1147008, 1409088]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Stock : Lower s67Mask s67StockWords s67Goal 9 := by
  apply essentialLift (witnesses := s67Witnesses) (cut := s44Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s44StockWords) (by decide +kernel)
  · exact s44Stock
  · decide +kernel
def s68Mask : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa0000aaaa
abbrev s68Goal : Nat := sGoal &&& s68Mask
abbrev s68StockWords : List Nat := projectDAGStock s68Mask sBase [1, 2, 3, 5, 6, 7]
def s68Fact : (Nat × List Nat × Nat × Nat) := (s68Mask, s68StockWords, 9, s68Goal)
def s68Witnesses := unpackWitnesses s68StockWords [594561, 67201, 868993, 330369, 1147521, 1409601]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Stock : Lower s68Mask s68StockWords s68Goal 9 := by
  apply essentialLift (witnesses := s68Witnesses) (cut := s45Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s45StockWords) (by decide +kernel)
  · exact s45Stock
  · decide +kernel
def s69Mask : Nat := 0xf000f000f000f000f000f000f000f000f000f000f000f000f000f000f000f
abbrev s69Goal : Nat := sGoal &&& s69Mask
abbrev s69StockWords : List Nat := projectDAGStock s69Mask sBase [0, 1, 4, 5, 6, 7]
def s69Fact : (Nat × List Nat × Nat × Nat) := (s69Mask, s69StockWords, 10, s69Goal)
def s69Cuts : List (Nat × List Nat × Nat × Nat) := [s47Fact, s48Fact, s19Fact, s26Fact, s35Fact, s37Fact, s46Fact]
def s69Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[17, 18, 34, 66, 96, 130, 160, 192, 17, 17, 17, 17, 3, 33, 48, 65, 80, 129, 144, 3, 3, 3, 3, 3], rfl⟩
def s69Sample : (Nat × Nat) := (0x48340a0d040b0482c1482c060b040a8442a148249209140a45028301208a070181c0826110984066128148a0512094482430190c0442180c86031108c442230188c0422280486012080480412080440211, 36)
def s69Witnesses := unpackWitnesses s69StockWords [74384, 598657, 337040, 876688, 1155216, 1417296]
def s69Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0xf073900000c4aa7000000028200271002616b0000014600000488c606c01 0x2e940749280cbd3861e88acc4e164a7078d053466a1a3290418a09bd100d25864f44146218930e1c0c86a0637073108118803066a143340c4a00518d0c24a020f442f62707b108398705a94e0d4a1158d3ca469c16343091a1030c519e4a08ef440761c33193918c840c636237a201b0e189e8908c434261c12250c1126e0492c717a24ab10d458706a9431549b88a4b1a06869033708195828c54046280003f 10 4 13 5 3 4
def s69Data : (Nat → Nat × Nat) := fun i => decodeNode 5 17 0x3d3ade896940bca75a4dc38872f449e1c4a4b03e889c424e1c265093280c3434b1a28d0926561c38331b18c54326e2c381c9608c50207e0 i
def s69Tags := dagTraceTags s69Mask 36 (dagTagBases s69StockWords 0xfff800000f007ff0000f07c0fc0cce638e3f0098279fc3371de783 0xaaf00000050053c020050280f10ccc630c3a0008430c43331ce381 36) 9 s69Data
def s69States := dagTrace s69Mask s69StockWords 9 s69Data
def s69Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 5, 7, 6] 0 i.val)
def s69Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 5, 7, 6] 0 i.val)
def s69Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s69Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s69Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 5, 6] 0 i.val)
def s69Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 7, 5] 0 i.val)
def s69Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 7, 5] 0 i.val)
def s69Move3Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 5, 6] 0 i.val)
def s69MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule moveStages [5]), s69Move0Map, s69Move0Inverse), ((moveSchedule moveStages [6]), s69Move1Map, s69Move1Inverse), ((moveSchedule moveStages [19, 5]), s69Move2Map, s69Move2Inverse), ((moveSchedule moveStages [6, 5]), s69Move3Map, s69Move3Inverse)]
def s69Moves := dagMoves s69MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Autos : DagMovesOK s69Mask s69Goal 256 s69Moves := dagMovesOfCheck (by decide +kernel)
def s69Check := dagCheckNode s69Mask s69Goal s69Chart (dagKnownCloses s69Goal s69Cuts) 26 s69States s69Moves s69Links s69Sample s69Tags
def s69RootAt (token : Nat) : Bool :=
  let s := rootState s69StockWords 9 token
  !dagAllowedRoot s69Witnesses s.2.1 || dagLocal s69Mask s69Goal s69Chart (dagKnownCloses s69Goal s69Cuts) s ||
  dagRef 26 s69States s69Moves s69Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69RootBlock0 : treeBlock 0 64 s69RootAt = true := by decide +kernel
theorem s69Roots : dagCheckRoots s69Mask s69Goal s69Chart (dagKnownCloses s69Goal s69Cuts) s69Witnesses (dagRef 26 s69States s69Moves s69Links 0) s69StockWords 9 = true := s69RootBlock0
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Block0 : treeBlock 0 16 s69Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Block16 : treeBlock 16 10 s69Check = true := by decide +kernel
theorem s69Verified : treeBlock 0 26 s69Check = true := (@treeBlock_merge 0 16 10 s69Check s69Block0 s69Block16)
theorem s69Blocks : treeBlock 0 26 s69Check = true := s69Verified
theorem s69Known : Known s69Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s46Stock) s37Stock) s35Stock) s26Stock) s19Stock) s48Stock) s47Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Stock : Lower s69Mask s69StockWords s69Goal 10 := by
  apply lowerDag _ _ _ _ s69Autos _ _ _ s69Known _ s69Roots s69Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s69StockWords; decide +kernel
  · decide +kernel
  · simp only [s69Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s70Mask : Nat := 0x33003300330033003300330033003300330033003300330033003300330033
abbrev s70Goal : Nat := sGoal &&& s70Mask
abbrev s70StockWords : List Nat := projectDAGStock s70Mask sBase [0, 2, 4, 5, 6, 7]
def s70Fact : (Nat × List Nat × Nat × Nat) := (s70Mask, s70StockWords, 9, s70Goal)
def s70Witnesses := unpackWitnesses s70StockWords [74384, 598657, 338064, 876688, 1155216, 1417296]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s70Stock : Lower s70Mask s70StockWords s70Goal 9 := by
  apply essentialLift (witnesses := s70Witnesses) (cut := s49Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s49StockWords) (by decide +kernel)
  · exact s49Stock
  · decide +kernel
def s71Mask : Nat := 0x55005500550055005500550055005500550055005500550055005500550055
abbrev s71Goal : Nat := sGoal &&& s71Mask
abbrev s71StockWords : List Nat := projectDAGStock s71Mask sBase [1, 2, 4, 5, 6, 7]
def s71Fact : (Nat × List Nat × Nat × Nat) := (s71Mask, s71StockWords, 10, s71Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Stock : Lower s71Mask s71StockWords s71Goal 10 := dagShiftLower (width := 256) (moveSchedule moveStages [11, 1, 17, 13]) s65Stock (by decide +kernel)
def s72Mask : Nat := 0xff000000ff000000ff000000ff000000ff000000ff000000ff000000ff0000
abbrev s72Goal : Nat := sGoal &&& s72Mask
abbrev s72StockWords : List Nat := projectDAGStock s72Mask sBase [0, 1, 2, 5, 6, 7]
def s72Witnesses := unpackWitnesses s72StockWords [74384, 337040, 600208, 876688, 1155216, 1417296]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Stock : Lower s72Mask s72StockWords s72Goal 9 := by
  apply essentialLift (witnesses := s72Witnesses) (cut := s50Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s50StockWords) (by decide +kernel)
  · exact s50Stock
  · decide +kernel
def s73Mask : Nat := 0x303030303030303030303030303030303030303030303030303030303030303
abbrev s73Goal : Nat := sGoal &&& s73Mask
abbrev s73StockWords : List Nat := projectDAGStock s73Mask sBase [0, 3, 4, 5, 6, 7]
def s73Fact : (Nat × List Nat × Nat × Nat) := (s73Mask, s73StockWords, 10, s73Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Stock : Lower s73Mask s73StockWords s73Goal 10 := dagShiftLower (width := 256) (moveSchedule moveStages [11, 2, 3]) s69Stock (by decide +kernel)
def s74Mask : Nat := 0x505050505050505050505050505050505050505050505050505050505050505
abbrev s74Goal : Nat := sGoal &&& s74Mask
abbrev s74StockWords : List Nat := projectDAGStock s74Mask sBase [1, 3, 4, 5, 6, 7]
def s74Fact : (Nat × List Nat × Nat × Nat) := (s74Mask, s74StockWords, 10, s74Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74Stock : Lower s74Mask s74StockWords s74Goal 10 := dagShiftLower (width := 256) (moveSchedule moveStages [11, 2, 17]) s65Stock (by decide +kernel)
def s75Mask : Nat := 0x2222222222222222222222222222222222222222222222222222222222222222
abbrev s75Goal : Nat := sGoal &&& s75Mask
abbrev s75StockWords : List Nat := projectDAGStock s75Mask sBase [2, 3, 4, 5, 6, 7]
def s75Fact : (Nat × List Nat × Nat × Nat) := (s75Mask, s75StockWords, 9, s75Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Stock : Lower s75Mask s75StockWords s75Goal 9 := dagShiftLower (width := 256) (moveSchedule moveStages [16, 12, 18, 4]) s72Stock (by decide +kernel)
def s76Mask : Nat := 0x5555000055550000555500005555000055550000555500005555000055550000
abbrev s76Goal : Nat := sGoal &&& s76Mask
abbrev s76StockWords : List Nat := projectDAGStock s76Mask sBase [1, 2, 3, 5, 6, 7]
def s76Fact : (Nat × List Nat × Nat × Nat) := (s76Mask, s76StockWords, 9, s76Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Stock : Lower s76Mask s76StockWords s76Goal 9 := dagShiftLower (width := 256) (moveSchedule moveStages [1, 3, 0, 4]) s68Stock (by decide +kernel)
def s77Mask : Nat := 0xffffffffffffffffffffffffffffffff
abbrev s77Goal : Nat := sGoal &&& s77Mask
abbrev s77StockWords : List Nat := projectDAGStock s77Mask sBase [0, 1, 2, 3, 4, 5, 6]
def s77Fact : (Nat × List Nat × Nat × Nat) := (s77Mask, s77StockWords, 11, s77Goal)
def s77Witnesses := unpackWitnesses s77StockWords [41552, 831568, 1090113, 304208, 1368144, 567376, 1630256]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s77Stock : Lower s77Mask s77StockWords s77Goal 11 := by
  apply essentialLift (witnesses := s77Witnesses) (cut := s56Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s56StockWords) (by decide +kernel)
  · exact s56Stock
  · decide +kernel
def s78Mask : Nat := 0xffffffffffffffff0000000000000000ffffffffffffffff
abbrev s78Goal : Nat := sGoal &&& s78Mask
abbrev s78StockWords : List Nat := projectDAGStock s78Mask sBase [0, 1, 2, 3, 4, 5, 7]
def s78Fact : (Nat × List Nat × Nat × Nat) := (s78Mask, s78StockWords, 11, s78Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s78Stock : Lower s78Mask s78StockWords s78Goal 11 := dagShiftLower (width := 256) (moveSchedule moveStages [5]) s77Stock (by decide +kernel)
def s79Mask : Nat := 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff
abbrev s79Goal : Nat := sGoal &&& s79Mask
abbrev s79StockWords : List Nat := projectDAGStock s79Mask sBase [0, 1, 2, 3, 4, 6, 7]
def s79Fact : (Nat × List Nat × Nat × Nat) := (s79Mask, s79StockWords, 11, s79Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79Stock : Lower s79Mask s79StockWords s79Goal 11 := dagShiftLower (width := 256) (moveSchedule moveStages [6, 5]) s77Stock (by decide +kernel)
def s80Mask : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff
abbrev s80Goal : Nat := sGoal &&& s80Mask
abbrev s80StockWords : List Nat := projectDAGStock s80Mask sBase [0, 1, 2, 3, 5, 6, 7]
def s80Fact : (Nat × List Nat × Nat × Nat) := (s80Mask, s80StockWords, 11, s80Goal)
def s80Witnesses := unpackWitnesses s80StockWords [7694, 856705, 329345, 1131137, 592513, 1409665, 1671745]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s80Stock : Lower s80Mask s80StockWords s80Goal 11 := by
  apply essentialLift (witnesses := s80Witnesses) (cut := s66Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s66StockWords) (by decide +kernel)
  · exact s66Stock
  · decide +kernel
def s81Mask : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff
abbrev s81Goal : Nat := sGoal &&& s81Mask
abbrev s81StockWords : List Nat := projectDAGStock s81Mask sBase [0, 1, 2, 4, 5, 6, 7]
def s81Fact : (Nat × List Nat × Nat × Nat) := (s81Mask, s81StockWords, 11, s81Goal)
def s81Witnesses := unpackWitnesses s81StockWords [74384, 860801, 337040, 1138832, 600208, 1417360, 1679440]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s81Stock : Lower s81Mask s81StockWords s81Goal 11 := by
  apply essentialLift (witnesses := s81Witnesses) (cut := s71Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s71StockWords) (by decide +kernel)
  · exact s71Stock
  · decide +kernel
def s82Mask : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev s82Goal : Nat := sGoal &&& s82Mask
abbrev s82StockWords : List Nat := projectDAGStock s82Mask sBase [0, 1, 3, 4, 5, 6, 7]
def s82Fact : (Nat × List Nat × Nat × Nat) := (s82Mask, s82StockWords, 12, s82Goal)
def s82Cuts : List (Nat × List Nat × Nat × Nat) := [s56Fact, s59Fact, s62Fact, s65Fact, s69Fact, s73Fact, s74Fact]
def s82Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 17, 18, 34, 40, 66, 72, 96, 130, 136, 160, 192, 3, 10, 24, 33, 48, 65, 80, 129, 144, 3, 3, 3], rfl⟩
def s82Sample : (Nat × Nat) := (0x48340a0d040b0482c1482c060b040a8520980c261209248245029140a0c0482281c0607028160305828148a051209440442180e03038180c86031108c4142a0c068141a00844140b0182c0209, 34)
def s82Witnesses := unpackWitnesses s82StockWords [74384, 602256, 860801, 337040, 1138832, 1417360, 1679440]
def s82Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x1 0x7f 2 1 7 1 1 1
def s82Data : (Nat → Nat × Nat) := fun i => decodeNode 1 8 0xfe i
def s82Tags := dagTraceTags s82Mask 34 (dagTagBases s82StockWords 0x3fff00000f003fc000380c0fc0cdf3fbee006030c77004c249d8c8e0618f 0x2ade000005002b800010040b80cde3f3c8002010474000404158c860208b 34) 11 s82Data
def s82States := dagTrace s82Mask s82StockWords 11 s82Data
def s82MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := []
def s82Moves := dagMoves s82MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s82Autos : DagMovesOK s82Mask s82Goal 256 s82Moves := dagMovesOfCheck (by decide +kernel)
def s82Check := dagCheckNode s82Mask s82Goal s82Chart (dagKnownCloses s82Goal s82Cuts) 1 s82States s82Moves s82Links s82Sample s82Tags
def s82RootAt (token : Nat) : Bool :=
  let s := rootState s82StockWords 11 token
  !dagAllowedRoot s82Witnesses s.2.1 || dagLocal s82Mask s82Goal s82Chart (dagKnownCloses s82Goal s82Cuts) s ||
  dagRef 1 s82States s82Moves s82Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s82RootBlock0 : treeBlock 0 64 s82RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s82RootBlock64 : treeBlock 64 64 s82RootAt = true := by decide +kernel
theorem s82RootVerified : treeBlock 0 128 s82RootAt = true := (@treeBlock_merge 0 64 64 s82RootAt s82RootBlock0 s82RootBlock64)
theorem s82Roots : dagCheckRoots s82Mask s82Goal s82Chart (dagKnownCloses s82Goal s82Cuts) s82Witnesses (dagRef 1 s82States s82Moves s82Links 0) s82StockWords 11 = true := s82RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s82Block0 : treeBlock 0 1 s82Check = true := by decide +kernel
theorem s82Blocks : treeBlock 0 1 s82Check = true := s82Block0
theorem s82Known : Known s82Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s74Stock) s73Stock) s69Stock) s65Stock) s62Stock) s59Stock) s56Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s82Stock : Lower s82Mask s82StockWords s82Goal 12 := by
  apply lowerDag _ _ _ _ s82Autos _ _ _ s82Known _ s82Roots s82Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s82StockWords; decide +kernel
  · decide +kernel
  · simp only [s82Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s83Mask : Nat := 0x3333333333333333333333333333333333333333333333333333333333333333
abbrev s83Goal : Nat := sGoal &&& s83Mask
abbrev s83StockWords : List Nat := projectDAGStock s83Mask sBase [0, 2, 3, 4, 5, 6, 7]
def s83Fact : (Nat × List Nat × Nat × Nat) := (s83Mask, s83StockWords, 11, s83Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s83Stock : Lower s83Mask s83StockWords s83Goal 11 := dagShiftLower (width := 256) (moveSchedule moveStages [11, 2]) s81Stock (by decide +kernel)
def s84Mask : Nat := 0x5555555555555555555555555555555555555555555555555555555555555555
abbrev s84Goal : Nat := sGoal &&& s84Mask
abbrev s84StockWords : List Nat := projectDAGStock s84Mask sBase [1, 2, 3, 4, 5, 6, 7]
def s84Fact : (Nat × List Nat × Nat × Nat) := (s84Mask, s84StockWords, 11, s84Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s84Stock : Lower s84Mask s84StockWords s84Goal 11 := dagShiftLower (width := 256) (moveSchedule moveStages [11, 1, 3]) s80Stock (by decide +kernel)
def s85Mask : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
abbrev s85Goal : Nat := sGoal &&& s85Mask
abbrev s85StockWords : List Nat := projectDAGStock s85Mask sBase [1, 2, 3, 4, 5, 6, 7]
def s85Fact : (Nat × List Nat × Nat × Nat) := (s85Mask, s85StockWords, 10, s85Goal)
def s85Witnesses := unpackWitnesses s85StockWords [594561, 860801, 67201, 1131137, 330369, 1409665, 1671745]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Stock : Lower s85Mask s85StockWords s85Goal 10 := by
  apply essentialLift (witnesses := s85Witnesses) (cut := s75Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s75StockWords) (by decide +kernel)
  · exact s75Stock
  · decide +kernel
def s86Mask : Nat := 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000
abbrev s86Goal : Nat := sGoal &&& s86Mask
abbrev s86StockWords : List Nat := projectDAGStock s86Mask sBase [0, 1, 2, 3, 5, 6, 7]
def s86Fact : (Nat × List Nat × Nat × Nat) := (s86Mask, s86StockWords, 10, s86Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s86Stock : Lower s86Mask s86StockWords s86Goal 10 := dagShiftLower (width := 256) (moveSchedule moveStages [11, 1, 3, 13]) s85Stock (by decide +kernel)
def s87Mask : Nat := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
abbrev s87Goal : Nat := sGoal &&& s87Mask
abbrev s87StockWords : List Nat := projectDAGStock s87Mask sBase [0, 1, 2, 3, 4, 5, 6, 7]
def s87Cuts : List (Nat × List Nat × Nat × Nat) := [s82Fact, s77Fact, s78Fact, s79Fact, s80Fact, s81Fact, s83Fact, s84Fact, s66Fact, s69Fact, s71Fact, s73Fact, s85Fact, s86Fact, s67Fact, s68Fact, s70Fact, s75Fact, s76Fact, s51Fact, s52Fact, s53Fact, s57Fact, s58Fact, s60Fact, s61Fact, s63Fact, s64Fact, s37Fact, s39Fact, s38Fact, s46Fact]
def s87Chart : Option ({ rows : List Nat // rows.length = 24 }) := some ⟨[9, 17, 18, 34, 36, 40, 66, 68, 72, 96, 130, 132, 7, 14, 28, 33, 48, 65, 80, 129, 144, 7, 7, 7], rfl⟩
def s87Sample : (Nat × Nat) := (0x48340a0d01834102c120b0500c02030120b0182c01cac40a8442a140a8100a010280389c4826038984825038940a251209248245029107238388c07231008803a1d028502a15008440a0d0282402080482281c06070209844261039848060101801c600e170a0581816038580c160a0540e150a05218148a051209441c4e07130144a209240e470711882450391482430e0f060380c0e060340e0d0a032180c86031108c41c2e070b0142a108a41c280389c1c26108940e2507090422307088381e07078381d0c0680e171805838160a0580e160e05428152804860121804402110703c0e0f0e0340e0d02834140b0182d0209208244209070240209, 112)
def s87Witnesses := unpackWitnesses s87StockWords [74384, 864400, 1122945, 337040, 1400976, 600208, 1679504, 1941584]
def s87Links : (Nat → Nat → Option (Nat × Nat)) := 
  dagLookupLinks 0x158a1ab0a80002abc20000aa9355406a6200000a961000029fb14d35a680d2d38000149cca2ffd097400014221a0f15070682c741039f788000000013ec19f224ea7a7295392100004da566a95336f986acbf9e5f832f4400004bb8e57752ac794874a386518328a194124a0064f85260e9293c9404000124c291f3c8f06474323810000488ae440320108f93c7c063c111c4e8d8546a8e348718cc8c4145bb62d07160400004504227c313838991c4b0e2543128188b4c402e1f850f63879143b0e1a990cc4852a4259e10d107c58383416ae0a0b042781c2c0b9604c900707efa3f705fb42fd817e91bf405f984fb2d7d143e789f344f8897c30be089f002f6ca7b4100001ec84000000003d4a40000f4c379873c82000000000787480001df540000000000001dd5000000000000000000000076c4bb585d626ea657501ba519d09000007410b97c9c6aae1ad7063b7e29bb9c00006ed0b7491b52ad94a6c90b6215ae94d5cc00003541800000000000000001a84e0000699434b89a4c8d22268c280001a246d0e267d5337b9989acc2165a3b2c859602cae16560b27219342c8896411b1e158e46c6666320b17118ac6c54161e630e8586c4c341616230a0984c2000060f200001838200000000000000000000060642fea57ec4bf035f612fa857c0abde15ed12f6057ac2bd415e14af0040000bbe15dc1ae92970deb6705ad3000016a48000059b72c7b162c8b12257982b4440000ac650000000000000ac415610aaab15068a7e20000299b14bc8a50751d5a883543c2a1075070a83054142a0814fc427d853c929de34ea2a738d384c9c014dc226c8d35c4996c4ca0a640931c200004c320000130820000000000000000097294b04a50bd265092a448f324324000090634709a351800008cc445b5800000000000045818000115c2892e0000000010f5886e60000218990958829141020000000007fb33f921f7a80000000000001f68800007d813e159ee90000000003d9200000000000003d2380000f198786300001df14ed1475c6000000000e9ce000039f41cf04e742726a00001c904e4427201000000000e28c70670000000000000000037b41bd04dade6d2236619b208d7ca6b8335a11ac84d50a6a6135111a804d3c269c134d09a604d094682100001a004cf46662c00000000000006601000019784c9546389000018b1800000000000000000c3ce0000308398384c1446081301180000bfc45fc10000179ac00005e41000000000000000002f1097424b9c25ca22e4080000b8460000000000000000000002d9400000b60259e92bf8157c0a7e00000000014f04a59051c828d080000a1124f4a2790935b800004c87261192e149510494a24909219890824821240091f848e0e46e12303917088ac64522225211204884643e2216490a8484c4424100001078c000000000000000000000410720040f9b40000000000000f9047b4a000000000f6047a463c661df20ee8876863aa500000e5a8720600001c610e0946ecc00001b72000000000000000000d914000035c4000000000000035a100000d604000034c619c50c9a461d80000186080000614230430000000000000302117c28000000002f6117818b9185c422e0116f08b7045b042ca716408b18458442ba40000000000000000015c08ab180000000015508a90c530c28a70000000005102278813440998400002549120508f84445c000010a38838c408a1f4800000000000001f210f428000000001e610f018751838141be10d9306c0435c21ac10d508671c334218c70c410608c2fc417640ba085b8c2d4415890ab0854882a0200000a518000000000000000000000278e12c808968429020c4100307b2800001c540dc300000360819ca0c26000002e9000000000000000000160a0000054200000000000000530800001482000004c3021280e5200000000000000e0206650000000000c8205e3029300eb000780001 0x2a0014053fb746a158b2c3130e26784b8ccee9656a292b312ca535a594a0b0f0937637d258cd718a8e781b89cee3650a286b252c8d342591a0835c31d037c628142816407800980c40080a74050c30b0e18de496335a62a06b463a06f0c50061004035a6286181e8932c319625862cb4b0c4d6375870cd624d8e5833294b06590960c9a0d618a40dd31000c03146a6406c14d80a429a014053201e0a5f6e80d58c7029cc3485318686a558cec2fb0e1a964b3b4cc965995d2b312ba535a574a0b0ee9376371258cd518a82961b384cc365395c6b252b8d342571a0840632b06a863a06e0c50295033810403701dc02602f8020e80c3415235660a464cd243bd9d85e7a24cf2c6789558b2d2ab135876621b1b6c3866a526c73c999ca5532c84aa64d0808c6e0d498a40db310190e367020468603b0c7c05e18a05215640a4b0d0147c96185d7a2349ac6599518b3129b1358da61c33509360934cca72a1964a5332683506290368c4002e8c50a90aae05212506171e89125b165a4b626b1b2c38669d26c525996424b326834e6290364c4002e0c5128faae0d1f2500a3de89542316de84627b508c43616d871544a56e24a4acbd1294f692929ad44a50de4a4a0b0ea9376361258cd318a92891ad94943591a2469e1250d342891a18c9434108046560d30c740d818a250805b1a1009e142010c08001b80ea013016c010348e1a0291928051cf587a0d8ced41b13d85a61c3d1096769252cb328a565a884a7bc9294d8945282c3a24dd8d7496334a62a1a206ce1248d94e511ac851034f192469a5288d04200195834a31d035c628341819c28302780fe03701d002602d00201a23141cec36406846380d00c702897b21ca4364067c638ccf18a01fe194033c31c39ff6e873c61c828cc3485178680a2aae454449c82887b903fe9650a1d2b3121a535a434a0b1ac92c668cc5473a8dc81fd195033a31c01640101423d90e7edba050b5722a0e4e4141bdc8e7dc34053d5670a52acc149d570a8d933051af6692198ced41316d85861c4ce89676a192b6d2fa5662424a6b48494161cd26ec6aa4b199c3151ce83670a186b612f8d64a421a6848434107f06560ce0c740d518a190c0670a080b603f00dc07300980b0008615e4a172b3d96a567acb1a8f44666d884b2b25952564ac8336935035125802b988019a314050186869f9ecec2b3d11a7f633d4d4c65b9698b352d3135872621b1a6c38666526c13f999d26a332acb46594968c9a0fd98dc19931481a662009f86ce03e8d0c07218f80ac3146156ab8c38c96d8d29283330f4e07e989e0cc31040d261c00f895b01c526e02aa4b027caae490b25b61524a1339bd6d8707a7b1a2f44665d884739a56c1f94a1832e9350345258642996c07b32780e062b0150c4033dd57027d92d84f72509211eb70423d3d8537a24ce4c5b89c989ec37b10d8d061c332c93639c8cb6539193c1f831b832c6290340c406420d6c8841a780f434301bc63e0298c5164dab8249b56419524e012a4990e26338144c6640568c500ac8c702761b21c46358288c6980ac0c702766320ca4c58094989813cedd027893904e1271099a4e0337499564993204dd25949264b012f49402777b904aef701945ec8128bd622404b8cc7a96588f52b20fba5358cf496332a62a09d46e45158dc0e1e1b2143c35807906540ab8c7004800404bb86807d9ecac673d1199462103c694205592680239880273c340ce356719aaacc12e557065a9330c82c6708d58b60fab1658cd61c332693618b8ccc0f118d8155314008c3140550c500a98c7015231404db2641941ec87128d9015118e02a031c09b64c80a78c70271dba04e187209bf0d013755c826c9390c9ef7208d12ca119a5358cc496332462a18b46e40f08ca814e18e008a00809930d00f9b1958cb61c33229360780c6c0a698a004418a029831c052cc5013400a0267c3403e49656329258cc818a81df195029431c010c0100a498a014849a028e31c09930d0927559864e9333192c38663d26c31619981de31b028c6280108628131819826201b028a31c09ab0d0134d59c266ab304cb55d0986ab8924c9986497b30c8096709812b60f825658c8496331c62a18ac6cc0ee8ca814418e0082008091e4e0322c99024592c04526703890cc851219601433140284c4009770d032455998c77a2331ac4218a92cc0ee250814149a008062019730d012f559c25caae0c8926609124b431fb19c23f62db18cc38663126c313999822732d03b66360500c5001f8c50256c34049125008f18b20f6b1358c561c33169360874cb00ed18d813f314007c314188c6c810e0d3013e18e0c36664086ccb009e98a0258c34048ef4418ed2b211da5341ec4a0b18892c6628c5430d0d6021a1a603b232a04f063801e80202194b20276934095b0d0129d59824d933048d25008e98b20f5b1358c361c33129361898ccc10c19601d831b027462800f0628b25c990e223320272628092e4b050a999062232c027062809530d0129c9402507ac8494f580915e8911ca59463e4ac83d49416309258cc418a82521b3142836418846b00eb8ca813718e007600804d863812849902171a6026a31c09324c810b193013431404972580854c9809998a01323140262628592eab8126494024b7a203d294d6305258cc398a81d6195026031c00e801012761a024d9280494f5807a12ca11ca5058c0496330c62a08506800ea8ca812f18e0072008084d2b009724d061232c042464c04b4c50108a56012c49a04206641880cb009598a0248c34048f566091aab8122c998238626b17ec38661526c30f999820e32603a863604a8c5001c0c51984314041a34c074c6500948c7025ac3404b3567095eacc12ad570251933049ef670925ecc1223d1063d4b3848695b08dd29a119250c1e64a0b17c92c660cc5430f0d9820c1a603a432a04a063801b80201f3ab8047926487458b1093a4d01d13380380634049cc500f955c16399320472f4c87412e109318a01cd1ac037e328048c63811c496212549a039866406f8c6809118a05e97a643969408484c500e58d301bd194024231c98e6ac811dc9c023e9320bd0f58b82d2c90e725021243140c1236407286b00de0ca012018e4392c4c847d2680e499601bb31a023e628a8292b10e4250211e3140c1435807206980dd0ca011e18e438ec4c84752680e399601b931a023a62887192c908e18a01c41a00370328046863908da4d01c3326036e6340464c5011e61a023bab3047555c88e64cd11c49402397b30470f44a82d2cc118a50a1c24a04230628182c6cd1188d381c21a6036c3280460638120edd2240c39447f86888f6ae412049ca234933046926507c24c811fc94023d7b9046ef58a8212e4118253a1c14a6422662818206e51180d981c11b20362328044c63808918a011118e022031c08c52b01038d6010f18e021c31c08c58b00868c70635dba046b86818d2ae411a5598633939046726618c9ee41193d986304b9046096618186e41030d9810c18e145586808aa4a010ebd601d14b293a294d62f5258cc118a803618a144b264085d898b0b49902167a6045986828a64a0b0a3d6021462013a06650734c9ac5e188198118f006a008084e4b03083d602107a6041f25808ab0d0114d598228aae1449266087decc1073d301cc4acb17692c6600c5401a0c50e15ab20445264284a4c85104960a22aae04452502881e8811030e01cb320939663562e8c40cbf8c780330040c212580849ec81103d60226c34044b25938524b011249402237b30434f640885eb010fb0e020b32c839464d2738c6ac5c988197e18f00640080866ab8509c9402137a2039294d2725282c5c24b197d3150062314086eab85093d1021261c041464d0720c824e418d58b731032f831e00c001010cd570a1592d14232500855eb4108bd101c74a6938e94162d9258cbd98a802f18a042d55c0855e8850830e09c632c838863562d4c40cbd0c7802e004042755c084a4b4108c9402107ad041ef44070d282c5a24b1979315005a31465e063810ed57021c92d843525a08624a050bbd6ca147ad141cf44085d8b610a316820e61c041265b0834c9e503990c1c2320840e6372708c6ac59988197718f0058008171a4b01053d905b33265b6a63494546382da19011b431a4a2c31c082a4b00e33d909c66320b6a64046d4c6928b8c701d0ab814172642741ee0105b1902096260b6465846c8c8128a0c7020762c045d86828b6ace515d598a27aae143d26608b5ece115bd982277a2043cc660831898104199ca0632d83826590818c864e099058b231032ec31e00ac01033961a0274ab384e555c19ae4ce32fc99826b92d84bf25a096e4a03213d982427ad0c6c96708d92b6117a53c1e54a6b16292c65d4c543028d982051ad036032a038463801500201f26381bd8c6427b18b00f631319df4b84bb296487652b0ceca53017431a03be37037646c84ec8d601d91a613d6f6407adeb10ec31919d862c02e69402760cc80ec19609e963203d2c5817a58990eb25919d64ac3bac94c05c8c684eb0d901d61ac0bac34c08064c80f431c0dea6320bd0c5827a9898ceaa5c25d74b23baa958875d2980b898d01d51b81bae36417546b04eb8d3017018e03fc658874cc98ce9990016f1941bf7b74080f0e410161a0a00ab9040127237dd8e40ffb1981f063213ccc5807998992f225c99fd4b333ba96487492b0ce9253016e31a1bc837207f46cc0ee8d909d21ac03a434c47cdee0af6bd911ed7ac53c0c70b7698c94ed316016d4a023c06705768cc88ed196016c7ac03f586837da4cd2f1bd9816b6261bc696617e70d00fdd59c1f9aae1beaf6627d5eb52f1319a1e262d02d49403788ccc4f119681f29382bd126447a24b00f63dc05ea7b203d4f5887352e12e525921ca4ac139a37037286c84e50d601f6c340be756607beab82f6c99a5d16331ba266607cf0d00f955981f1aae23d126617a1ecd2e82598dd01b30bdf86807beab82f3c9981e792d4b9ec66873d8b46e799989cf32d4392c582724cb12e425621c84a61b9035827206990e3b1609c732c03d2f5887112c92e5a5609c41b21b9635807a5eb10e325009c61a0438ac4c2714c980f6e1a01ecab303d755c07aa4cc0f43d981e77a24b9c96687092986e70d989c21a60beb86807deace0fad5705f49338be126607d24b60f849681ee9280bccf660799eb52e0a59a1c14ad1b8236627046b40efc9c15d593223ab2580765ee02ebbd901d77ac03a097017392c80e725621bf3384b7866486f0cb00858ca010a4a003c78681782acc0ee55705da9330ba2c6617012cc08498d0108194020e634041865008298d01e0c3403bf566077aab88eac9985d57b30b9a96616fcccc0820ca01034a00bb98680772ab82ea49981d492d0b98c6607318b42df25981be4ad020463407258b00dda56010131a0b9095807212982dd19601ba3260200328071d8b00dca5600ff31a03acf5807192c82e5a5621b83320b7a65803f865007e8ca01d67ac038894006e0c8007e0ca01c3626036e94c03ecc6807d0c701dac3403b35660762ab80ebc9981d57b303a8f4417292cc0e125305bc33303a665a06d8c9807c8ca01c97ac0b8cc5807198980e2bd615c47ac0390c64072d8b12da99615c47ac0388c40070de982e349601c87b20396f5816cccb02da19301c9aae039125a071e4a00e33d681c57a20388c5a070d8702da99681d1c3403a1566073eab80e749981cd7b30398f4407298cc0e131305b23330376f5803c0c50adc3d601b862001de31c06dde9807718a00ed18e4b7125806e9ec80debd601b532c01d831c03acc500da19300ea18e01d262803a063807398a01bbaae037525a06e64a10dc3d6a1b77a20370c5a06dd8700d999680e618e0368c5806d1e990dabd601b54ac036694007030d10dfd59a1beaae437926606fdecc0df3d101bc633036cc4c06c8ccc0718c705e2c3403c9567078aab82f0c99c5dd93303c325b07764b40edc9405d27b303a4f5a17052cc0e0a5685b1333036265a03886506fc61a11fcab393f155c17f24ce0fe496c1f89281bcac6627958b40f2b13a5b04b3436095a66c129c0ad98d0db01b3136035a06c069c6ac8dc0d581b2034235824f869809f0d0006e0089a7a66424f4cb009e99301ad014035986806412ca6c5256498a4a6831494162992580ba18a81ab1b3029436434f06b049e0d3013c1a000da01100a40106cde1a09a8ab3035126626258b20c4b1358a561c02e69363568ccc49d196013a32600d831d00a06280d3c9601333321a7265824e0c984989960131326234f55c169e4a00d3bd109874ac830e94d161d282c5224b0172315234035a24c06b02d00d381301a6034034214c068003580440270040b5186806a24a00d33d601864b29b10959161929a4c425058a349602e262a167c6cc0978d90d371ac033e34e14bc69849b8d0006a008804c00806930d0cb798a019e1ac125234c04a46800d0316017018e1b358683566acc0d155701a1933133ef66067d8cc0cf193498432083086356288c400b78c780250041b3386806baace0d555981a9aae134b2660695ecc6caa59c1a34ad831c959260d29a0c1a5058a149602dc62a355c6cc0ce8d681441ac125034c04a068003480440240042a7696444ed2b00cde1a1191632ab16c59462d89ac5030e016d49b03346664534cc8a9f996113f32600d031d008c628c4fc94016c7a700ce93500892580cc5570d947adb13cf4405ad8846ab25680663148042620165eab80ccc96c1979281b26c5b264d89ec4eb0e016a49b1aaa65a2554c9c0328c7402018a0321270561a4c88c3496018a7b80b10f640621eb04c0a5c0d7e4b212fc958642cc504918dc0d201b2124035864298800ca61a0591ab3031b55c162e4cc2c1319990949a1a4e6666420c50c83a4d1906314320a93406470d00c8559818faae230d2661619ecc2c0a5999043141a4c366640d8802c6e1a018daae0b0b26606164b42c0319818062d32049343494ccc492996817d62c3202934247ccb02be256017c4a6320062834786b048f0d3017b62c31fe9342474cb00c3bd6097a4b20afe95863f8c5048d0d90d211ac31fa628061deb00bd25018fc314123834005e5898c7da4d091b32602f064063e86380c5e1a018aab3031355c06224cc0c33d981857a20afc96605dd298c7c98a0d241b3030835a24606980bebd6157a7ac02f4c4005e5e986bd496017c7b202fef5834546b068b0d3017daae02f925a05ee4a04bd3d689797a202f4c5a05e587068b8d681781a703058682606acc4c0557097e9330302f660601e880bf31981776261a28366164f0d00cad59c193aae0b25267163a4cc0c9496c18e92d0319250160decc0c1bd685764b302ec95a6388c506898d989131ad320c6649400cb10801931900320020c36434006b04800d301001a041fe95863fd29847f99600ff32641fa65863f4c98e7e99008fd1ac01fa34c13f46800b93d618fc33249fc65873f0c9907f19000fc1b219fc35813f069847f0d001701a641f434063e86686b6e1a0174ab302e755c25c64cc0b8bd981684ac92cc94d05992820afa4b250b33332de65a6410cb107c99318f93201a1636605bc6b40820d608f91a601f2340a41d2c9680a5629014a6220e6645404cb0880993016caae02bcf4494298b4685256856baae02db25b05ae4a06b4b16c96962782c4c390575871284a56a1094a71a1265a2424c9c0b2a5320f832611f034c05958982b4e1a0169aae0ad126605a24b40b3c9405667b302ccf5a15912cc0b2256816149649ee66683dccb467b8d988f71ad1ac5868258aab80b14940d6163312c2c5a058589d27b259a0f64ad31ec94e33d8ccc47b19680f632731e895883c9298c7925000f432c11e464c03c8c802af557015e92849eac5a83d589c67aa5688f54a71abb55c457e4b64aec94055f7ad82bef4f0575e89278a56a0f14a731e294233c4cb447899380f13211ad555c45ba4b64b5494056e7ad82dcf4f05a9e886b1a56c9634a782c6943058125a0ae24b24e232d41c464e6388c846710d688e21a701c434254ce4c8899c9605397b20272f58056b0d00acbd981537b28294f641545eb2a97bd601517a6a25ef4c050de880ac319813c6320a6ec5804dd898093199452432c824864d6270c400858c7801f004028555c626d87008524d801e31002ad55c15524b62a6c9681419280a7ef5a149d2b6089253d89a496021262a00746280a83d6053662c02a0f5805530d00a9d598152aae02a3266053decc29ab19811132c82206416264c400840c7801c004029155c626125808398a801b18a029755c625cc400830c7801a004029155c44d24b429a3d69896496020a62a00646280a3816814daae029925b052a4b40a4c944146928225ef5a14bd8b4291996c145327b12a620041063c00c002012d7b20a56f5804ade980a1557052e92d3128c38040d26c00b9880541aae028725b05064a02953d6812a7a70a4495b048929ec49a4b0102315002c31404eeab80973d1011f4a6b12492c0404c5400a8c5013daae025ac381478c9a08f1905891310020031e005001009dd57013892d0266f5a04b1e8808ea53589049601fe62a004c628a98bd601317a6027355c04e1e8809b31341306260256c380470cb2290993588f31001fc31e004801009b3d601327ac0262f4c54c64a00993d1013161c311c62003f463c0088020134aae0266f4404c189808d18d588d31001f831e0040010097557012d92d025925004adeb408ca50588c49601f662a003c62807d0c7013faae027d25b04f24b409d49401377ad026ac5b04bd8b409530e052032d825264f0460c8208798dd88b31001f231e003801008fbd600f03140a38c5804718990778c7011b7ac41dc6285469eb008f319012162c022e65883b0638a8d3d6011a62001de31c0465e9807718a00ed18e0a392580479ec8090bd6051532c01d831c03acc5008b19300ea18e01d262883a063907398a00e818e01ce628047eab808f496811d9280238f5a046de8808d316811961c022a65a0438c6c0730c701164ac022cf4c045deb028aa5601154a0024f868049aacc092d5701249330246f660445eb20913d101206330230c4c0450ccc08699080e318e021c64c043929828961a0112aae0a2326604464b42883d981107ad0a1ec66043d8b4286999810d32d020cf6453f1eb087e3d3010063209fcc5803f98990778d924ec1ac41d834c042aab8283c9681039280a02f5a03d52582781968107aae020d25a04164a087e3d684fc62d01e862013bc6b4281d57010392809f6f5a03ede9c079a4b04ee32d01dc64e03acc982750d300ea1a001d264c03f58990740d604ed1a601fac4c03a06680739900101aae020125a03fe4a007f3d680fc62d01f6c3803e0c8207918804ec1ad01f434e039868007c31300e532009eb55c03d64a027a3d680f47a701e6f4413c98b407931384e432d01c864e03ad898a7431300e849a01cec4093a1e9807531600ed62601d725003a9e9c074bd120e862741cec3803a129c073a4b00e518a01ca94003c2ab9077c96a0ee92841d8f5a03bd8b407730e00ec4ad01cc9400390628284d57010b92d82132501421eb62823d681087a78208f4e0409e8827cb1680f962709ee65b03dcc9e07b18840f131009c635a038c69c2aad57015792d82ab2501539eb62a23d6814e7a78288f4e0501e8829431681286270a2665b044cc9e086190d88a31001c431e00340106cb557119c92d932d2501671eb60ce3d3c1967a21aea95b25d529e0baa50d88949602b662a33846b44708d380e11a100c8011003001006f00a00ddc34019496533112b246225340c44a0816092c0298c540058c50cd4c3411b5566036a4cc461b1640c3626815ec38029526c00518800d992c21b355c13664a006cbd108c14ac818294d130528205724b00a43150012314136b0d006d49400d87ac018096533092b226025348c24a0815a92c028cc540040c500a231419a7868037eace06e55980dbaae11af266035decc667a59c0d64ad819095922f929a05f25040ac496014262a001c62806a61a10cb632a98ac59431589a055b0e00a049b000c62002aa4a004fbd3800561c01a555c3339eb6054bd1009e621000892c1346ab8069c96c0d1928199ac5b233589e05430e009d49b0006620032a4e0a6049910c092c0188f701309ec80613d608bc4b8197296422e52b004e18a009b620019d868132eacc063d5704c5933097ac66026926804c98a009849a012e6280259268065e1a00caab3019355c43024cc2603d984bc4b3012a6280251880263e1a00c7aae097f26602fe4b425db1980bb62d012693402e18b004924d04b74ac016e94c0244c5005b316009049a0182f5822d52c825d256008f314011c6280305eb005aa50008d3140168c4c0231268062e1a00c4ab3018755c030a4cc0603d980bf7a2097296602cd29804598a00b87ac296af5802d588005a3d30cb592c016ef6402e9eb005c55700b792d016d25022d5eb445a3d100b562d0168c3802f70d045e55988bbaae117326602f1ecc05dbd100b96330166c4c13370d0067d59c0cdaae099926713224cc066496c0c892d018d25012f9ecc05f3d684b24b3016495a0228c500573d60cabc34016156602beab8456c9980ad7b3015555c12a6ab8055c96c0a9928195155c42b24b645449404ac7ad8158f4f02a1e8804b9990c9132c112264c0244c8044825600904a6111c6580238c9824719000a47ac011a664323ccb0246993088f3201941868029aacc052d5708a39330146f663270ccc051196809532c111664c022cc8084c25914924ac212494c027eab864db16849eaae014125b027a4a064d256889a4a7012ef645235eb0846bd30091632091ec58023d89804dd57049892d01292501249eb404c557009792d012d2504235eb4246b168494aae01292501231eb40463d3808e626011cc4c024aab8048c968090928011ef5a02358b404630e049aaae013925b026a4a024cbd6c4957ad0132f4f0255e9c049bd1048b62d0116c4e3276ab8850c96c89d9280942f5b0285e9e04ebd10c8a32d111464e0228c8466855710d592d91a12501355eb606abd3c0d07a2196295b22c529e058a50c0a7496011262a0008628043edd0085c340909868021aace042557008093218fbb74020b0e4040e1a087fab900ff27201f30d023de1a007dab380f755c31eb0d083f559c87aaae08fd26701fa4b603d494006e19400da32801b0c680358ca007593200d432831cb6e803c61cc077c3900ed86821d2ae403a49c806919400d0634019d898038e1a00664a008e186801caace038557006531a00d6f5831a30d0037559c06dab300d955c21aa4cc0353d98067aae08cd55c01a24b60334940c65aae20d325b21964a0234bd6c0697a780caf4431bf0d0839d59c86faae08e726701ce4b6037c94006419400c202801830d002930e00431b2987a35920f469a01e8d0402918e8016314315f0d042ed59805d93300a2f4420f0cb201e1934028314801462001724b082e557045c92800b8f44014187041d0d6403a1a68874341009c63a0048c5045dc3400bb250016deb0027b0e00391b2987635910e469a41d8d0402618e8010314009463862b61a0062ab380bf566017aab842d499805a7b3009cc3831206ce02c8d6c0411ac906e34d00dc6820120c7400718a00af8680135e88822199543e32ca07c64d008cc52003188004caae0044c41001587002ad57004b928188e95b008526a00224b0454aae00ad25b01524a00253d10c4632d908c64f0080c5200198800507ac189b868014aacc028d57084f933009ef660132ab8225d57004d92d8097250312aab8827496c84a928089cf5b0139e9e0253d10043938287326440e64b001ebdc043b7b20076f5820d46e06190d908321ac003e31c0079268023e1a0444ab3008155c10fa4cc21b199801d314003831c006cc5000d0c700193140089868010eacc02155710399330872f6610d46cc00c0c7001749a08818680102ab821c499803892d086866600d0cb400b18a003132c002a62810c06b00180d3001418e005e658004cc5001d3d6082e1b2086635800486380088c7003a7ac005c3400040638016993000f314007d86800f6acc01e557003b9330072f6600e1e882190d9802c1a6001c31c00c5eb0a173d6002e620005af4c30ba4b00183d900337ac006355c00c24b4017c94082e7ad105af4400b98b4016b0e0036c34106b56620d2ab841949980357b30068f4400c98cc0163130446c340091567011aab8222c99c441933008b25b01064b401fc9404377b3006ef5a10ac6cc0158d6800d18e003436430506b040a0d300141a01026658004cc984088d600111a60822340009deb00080d90c121ac082034c2048680611e1a0029ab3005155c209a4cc0133d98c1f1b3004a35a00606b04070d3000e1a020366645054cb080a9930022aae183c95a1086ab8011c96c021928183a65a2074c9c00d3d914107ac2020f4c00518c82093160012626003d55c106e4b400bc9404157ad003755c006a4b400cc9410107ad0820c5a105eab800bc94040f7ad001ef4e0045898008b130015aae002925a004e4a00093d6801062d001ec381076ab800fc96c01d9280838f5b1061eb400e3d3c0187a7002cf4410398b40073138c20aae204925b20824a02123d6c0247a78040f4430346b44068d3800d1a10012f58301b0d0005d59800aaae10112660021ecc002d570404aae000d25b00124a0601d57100792d9007250101deb6003bd3c0037a218a755c41624b6429c9404587ad80b0f4f014de88024b0e0c2a1ad905434f00a86860060c7400218a1cf555c4a064b653d49406817ad8502f4f09e9e89241b16e083627b106c436005871302256e2044a7b408943618d26ec4424b18e03151c0835b281069e1020d0c1af19581c031d0220628641816c883027810604301e406e031804c00100400000ff 17 5 13 10 4 5
def s87Data : (Nat → Nat × Nat) := fun i => decodeNode 10 23 0xa2a0dba53f567a080514ee1a695014d32028a6403d4ce1a295dba52e367a540cf4ad59a82aae505868a4a4a1474942907a251ef58a39ecd4161a687c3450f572a1dec944bdca874acd0e35ba0aae541bd92847b950605ba09e9e00e1a27e333cfc3679fa4b73dd5727c9284f6f440076e93ac9ca757b94eac649d86e53ad59e05c344e755c8176e93661ca6cc344d95729b24c936c9ca6c92dc0b868982acf3000a268c344cf566982abb3061a2620334c403698aab930256e6092d40b5679730d12ed5725c92840b86890eacf21e1a258ab348786895aab921e1a2529284a436694a4cd21c992507b3c8786892a4a12549424b7a2496f58929ecd21e1a245ab348b55c9164cd22bd12434adc86f5a8176e91bc9ca3792846f2648f9ee51be1a238ab347155c8e1ecd1c3d12387ac46e95b8170d118559a30933460f668c18b118a59a304a7c0b868819ecf0361a22c7b340d8688a2acd145572287a240d86887e4b30fc9421f7b343f250889eb10fbd622061c43ec6681aab906c96e0daae43725a836ab90cc9420d62dc1b55c855e890ab16a0daae41f25a83e4a107bd6a0f7a241ec38834c9f06b1320663241325882989904999e0662c40e6438186b5028d0c01c393fb8687f64c900c9c9fd6333fa6587f86ccfec96db0ab3bf38687eaab8fcc941b0ab3bcd8687daab8f3496de6c343e35667c6ab8f8c969e6aae3df25079b0d0f3d599e7aae3cf26679deb0f4bd99e77a23cef5a79989cd8559db1c343c755c6c64b6d8e1a1deab33bd55c77a4b4d8d571dc92836386874eacce9d571d39333a6f58759ecce9bd11d332d3a6f5a6c70d0e15599c2aae385266709ecce13d11c27ac396c6670aab8e1c969c3928386f5a70de88e1b169c361c386c4c7092b4d8e1a1b27b3364f446c9eb0deb199b2aae36f25a6de4a0dbb169b761c36ec4c6c92b0d9bd31b44a03666666c8cb4d88d39b0195803567674050d6e1a1ab1b3357566676ab8cec941a67a234ef58699ecccee1a1a44adb3b55c67a4cccf3161a063333c64d6786b4cebd3ce1c3433466666a4b6cbd5719892832ef44386acebb61a194aae2ed25b5db0d0c7d5998faae31f25a5daab8c6c94176c34309566612ab8c24999847ac30ef66611e88c20d69847ad2ed8685ddeccbbbd11777ac2fec665deab8bc4969789282f0c5a5e1870bc0d39786262ee95a5d928670d5996faae2def585c9eccb78d31701ad2def4f5724b6b5d5716c9282d6f44572ab8b24969649282c8f5a591898b2a569644a1ab925058589cb0a4b55c7a7abb250579e88aea4b15c3151c3868561eccac31995892d9c555c55a4a07161a14fab329f55c53e4cca7bd61507b329ef4f38aab8a2c96d45aae29725a5164a2a2d5714702d28f250514c9ea2bd38e292da8355c50a4a0a0bd10e2aae25325b4a6ab89ec96929aae2772504a6ab89c3d11387ad252f584d98b694d571307a2260f444c587098b1313062d25355c4ae4b495c9412b7ad256c384a4c9e94b138e2c34229566452ab88a4999147b3228f44451eb090b19914aae23325a4664a08cbd69197a2232c5a4658708cb131147ac22af4c4592808a9999143279c555c4364b486bd690d62d21a94c438cb486990ce292d9c755c42a4a071bd3ce3aae20b25a4164a082bd38e3928206f4438eab87d4968fa9281f4f5a3e98987eb168fa61c1f434e3e989c71b130f83279c662138e4a0793d38f27a21e4c4e3c8c4071d570e462d1c8c3839189876a568e49281cef4e39de8873a538e74961ce940391280728c50e41a71c631e388684708c7401ab39ac02837b0d06ed598d6aae1ad250361e886cbd60d87b31ac95b359e9e44e1a0d492d9a355c34a4a068bd1089ab396586833aab859496cb2c34193566326ab864c968b2aae18f2502cb0d05fd598bfaae17f2662fdeb060bd98bf7a217ef5a2cb0d059bd98b37a2166f582e98cc59d570b492d1692502d18b45a30e0b462616695a2c928644d598adaae15af582b9ecc56bd3ca892d95355c2aa4a054bd10a849611356628aab8513d60a47b314465a289e9e45496c9eaae13f250279e8845496c8baae13725022de9e45d5709692d12d250259e9c45c940947a211755c2324b44649408c7ad118c4c2398b44630e08c627116642228c54448c5001dba10f5672130d042d570840218038721ff0d03fc990809390ff25b1eaace3de1a07caae0f72501e806e00e1cc74c390e98681d24c83ac9c87492d8c95671c30d038d570709280c95671aaacc3555706a7ac0d6f661a9e9e32c96c66aae0cf250199e88328ca06400980356716405030e1a060ab30b355c1664a02dbd105c7ac0b6f661646b62cbd3c02c340af25b152ab82ac940547a200556613eab827bd60507b309ef4f12a4b625d5704c928096f4412987001559c2bc3408f55c0ae4b615e1a042ab308555c10a4b415d570409280578680e2acc1c557038933070f580e9ecc1c3d10387ad0578680b1ecc163d102c7ac066c660b2ab816c9682d92805ac5a0b587016b1302c1ad05634300aacc12d570257ac04ef660946b412bd3c0d92d84355c08a4a010bd100d92d81d55c07a4a0073d3c0eaae03325a0664a00cbd380e92802ef4403aab807c9680f92801ef5a03d89808b1680f61c01ec4e038684068c7402ab301155c021eb004bd98087a780725b012ab802c940047a20063140080100083fc00 i
def s87Tags := dagTraceTags s87Mask 112 (dagTagBases s87StockWords 0xfffffffff0000000000000000000fe0000000fffffff00000000000001fe00000ff00000fffff8000000e181ff000c0ffe00ff8007fff0000041c0f0000f81e0e07c07800fff004138ef0008619e9863e77f0f8000000488f000195906531efccc601830030e83800637018ad1433fff 0x952ca715e00000000000000000104a0000000a4456250400000080082092000005220800538890206004e181fe400c0ffc00ff0005bbe200004150e00019a1c8a8752f920a42004158ea0099219a88676f5f0f82004000a8109001da00776a440d621838010ec3800237008ad04415bd 112) 13 s87Data
def s87States := dagTrace s87Mask s87StockWords 13 s87Data
def s87Move0Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 5, 7, 6] 0 i.val)
def s87Move0Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 5, 7, 6] 0 i.val)
def s87Move1Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s87Move1Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 5, 7] 0 i.val)
def s87Move2Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 5, 6] 0 i.val)
def s87Move2Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 7, 5] 0 i.val)
def s87Move3Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 6, 7, 5] 0 i.val)
def s87Move3Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 5, 6] 0 i.val)
def s87Move4Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def s87Move4Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [0, 1, 2, 3, 4, 7, 6, 5] 0 i.val)
def s87Move5Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 5, 6, 7] 0 i.val)
def s87Move5Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 5, 6, 7] 0 i.val)
def s87Move6Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 5, 7, 6] 0 i.val)
def s87Move6Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 5, 7, 6] 0 i.val)
def s87Move7Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 6, 5, 7] 0 i.val)
def s87Move7Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 6, 5, 7] 0 i.val)
def s87Move8Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 7, 5, 6] 0 i.val)
def s87Move8Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 6, 7, 5] 0 i.val)
def s87Move9Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 6, 7, 5] 0 i.val)
def s87Move9Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 7, 5, 6] 0 i.val)
def s87Move10Map (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 7, 6, 5] 0 i.val)
def s87Move10Inverse (i : Fin 256) : Fin 256 := Fin.ofNat 256 (permuteAxes [4, 3, 2, 1, 0, 7, 6, 5] 0 i.val)
def s87MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 256 → Fin 256) × (Fin 256 → Fin 256))) := [((moveSchedule moveStages [5]), s87Move0Map, s87Move0Inverse), ((moveSchedule moveStages [6]), s87Move1Map, s87Move1Inverse), ((moveSchedule moveStages [19, 5]), s87Move2Map, s87Move2Inverse), ((moveSchedule moveStages [6, 5]), s87Move3Map, s87Move3Inverse), ((moveSchedule moveStages [19]), s87Move4Map, s87Move4Inverse), ((moveSchedule moveStages [11, 2]), s87Move5Map, s87Move5Inverse), ((moveSchedule moveStages [11, 2, 5]), s87Move6Map, s87Move6Inverse), ((moveSchedule moveStages [11, 2, 6]), s87Move7Map, s87Move7Inverse), ((moveSchedule moveStages [11, 2, 19, 5]), s87Move8Map, s87Move8Inverse), ((moveSchedule moveStages [11, 2, 6, 5]), s87Move9Map, s87Move9Inverse), ((moveSchedule moveStages [11, 2, 19]), s87Move10Map, s87Move10Inverse)]
def s87Moves := dagMoves s87MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Autos : DagMovesOK s87Mask s87Goal 256 s87Moves := dagMovesOfCheck (by decide +kernel)
def s87Check := dagCheckNode s87Mask s87Goal s87Chart (dagKnownCloses s87Goal s87Cuts) 673 s87States s87Moves s87Links s87Sample s87Tags
def s87RootAt (token : Nat) : Bool :=
  let s := rootState s87StockWords 13 token
  !dagAllowedRoot s87Witnesses s.2.1 || dagLocal s87Mask s87Goal s87Chart (dagKnownCloses s87Goal s87Cuts) s ||
  dagRef 673 s87States s87Moves s87Links 0 token s
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87RootBlock0 : treeBlock 0 64 s87RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87RootBlock64 : treeBlock 64 64 s87RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87RootBlock128 : treeBlock 128 64 s87RootAt = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87RootBlock192 : treeBlock 192 64 s87RootAt = true := by decide +kernel
theorem s87RootVerified : treeBlock 0 256 s87RootAt = true := (@treeBlock_merge 0 128 128 s87RootAt (@treeBlock_merge 0 64 64 s87RootAt s87RootBlock0 s87RootBlock64) (@treeBlock_merge 128 64 64 s87RootAt s87RootBlock128 s87RootBlock192))
theorem s87Roots : dagCheckRoots s87Mask s87Goal s87Chart (dagKnownCloses s87Goal s87Cuts) s87Witnesses (dagRef 673 s87States s87Moves s87Links 0) s87StockWords 13 = true := s87RootVerified
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block0 : treeBlock 0 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block16 : treeBlock 16 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block32 : treeBlock 32 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block48 : treeBlock 48 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block64 : treeBlock 64 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block80 : treeBlock 80 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block96 : treeBlock 96 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block112 : treeBlock 112 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block128 : treeBlock 128 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block144 : treeBlock 144 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block160 : treeBlock 160 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block176 : treeBlock 176 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block192 : treeBlock 192 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block208 : treeBlock 208 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block224 : treeBlock 224 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block240 : treeBlock 240 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block256 : treeBlock 256 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block272 : treeBlock 272 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block288 : treeBlock 288 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block304 : treeBlock 304 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block320 : treeBlock 320 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block336 : treeBlock 336 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block352 : treeBlock 352 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block368 : treeBlock 368 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block384 : treeBlock 384 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block400 : treeBlock 400 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block416 : treeBlock 416 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block432 : treeBlock 432 13 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block445 : treeBlock 445 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block461 : treeBlock 461 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block477 : treeBlock 477 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block493 : treeBlock 493 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block509 : treeBlock 509 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block525 : treeBlock 525 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block541 : treeBlock 541 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block557 : treeBlock 557 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block573 : treeBlock 573 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block589 : treeBlock 589 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block605 : treeBlock 605 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block621 : treeBlock 621 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block637 : treeBlock 637 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block653 : treeBlock 653 16 s87Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Block669 : treeBlock 669 4 s87Check = true := by decide +kernel
theorem s87Verified : treeBlock 0 673 s87Check = true := (@treeBlock_merge 0 336 337 s87Check (@treeBlock_merge 0 160 176 s87Check (@treeBlock_merge 0 80 80 s87Check (@treeBlock_merge 0 32 48 s87Check (@treeBlock_merge 0 16 16 s87Check s87Block0 s87Block16) (@treeBlock_merge 32 16 32 s87Check s87Block32 (@treeBlock_merge 48 16 16 s87Check s87Block48 s87Block64))) (@treeBlock_merge 80 32 48 s87Check (@treeBlock_merge 80 16 16 s87Check s87Block80 s87Block96) (@treeBlock_merge 112 16 32 s87Check s87Block112 (@treeBlock_merge 128 16 16 s87Check s87Block128 s87Block144)))) (@treeBlock_merge 160 80 96 s87Check (@treeBlock_merge 160 32 48 s87Check (@treeBlock_merge 160 16 16 s87Check s87Block160 s87Block176) (@treeBlock_merge 192 16 32 s87Check s87Block192 (@treeBlock_merge 208 16 16 s87Check s87Block208 s87Block224))) (@treeBlock_merge 240 48 48 s87Check (@treeBlock_merge 240 16 32 s87Check s87Block240 (@treeBlock_merge 256 16 16 s87Check s87Block256 s87Block272)) (@treeBlock_merge 288 16 32 s87Check s87Block288 (@treeBlock_merge 304 16 16 s87Check s87Block304 s87Block320))))) (@treeBlock_merge 336 173 164 s87Check (@treeBlock_merge 336 80 93 s87Check (@treeBlock_merge 336 32 48 s87Check (@treeBlock_merge 336 16 16 s87Check s87Block336 s87Block352) (@treeBlock_merge 368 16 32 s87Check s87Block368 (@treeBlock_merge 384 16 16 s87Check s87Block384 s87Block400))) (@treeBlock_merge 416 45 48 s87Check (@treeBlock_merge 416 16 29 s87Check s87Block416 (@treeBlock_merge 432 13 16 s87Check s87Block432 s87Block445)) (@treeBlock_merge 461 16 32 s87Check s87Block461 (@treeBlock_merge 477 16 16 s87Check s87Block477 s87Block493)))) (@treeBlock_merge 509 80 84 s87Check (@treeBlock_merge 509 32 48 s87Check (@treeBlock_merge 509 16 16 s87Check s87Block509 s87Block525) (@treeBlock_merge 541 16 32 s87Check s87Block541 (@treeBlock_merge 557 16 16 s87Check s87Block557 s87Block573))) (@treeBlock_merge 589 48 36 s87Check (@treeBlock_merge 589 16 32 s87Check s87Block589 (@treeBlock_merge 605 16 16 s87Check s87Block605 s87Block621)) (@treeBlock_merge 637 16 20 s87Check s87Block637 (@treeBlock_merge 653 16 4 s87Check s87Block653 s87Block669))))))
theorem s87Blocks : treeBlock 0 673 s87Check = true := s87Verified
theorem s87Known : Known s87Cuts := extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s46Stock) s38Stock) s39Stock) s37Stock) s64Stock) s63Stock) s61Stock) s60Stock) s58Stock) s57Stock) s53Stock) s52Stock) s51Stock) s76Stock) s75Stock) s70Stock) s68Stock) s67Stock) s86Stock) s85Stock) s73Stock) s71Stock) s69Stock) s66Stock) s84Stock) s83Stock) s81Stock) s80Stock) s79Stock) s78Stock) s77Stock) s82Stock
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Stock : Lower s87Mask s87StockWords s87Goal 14 := by
  apply lowerDag _ _ _ _ s87Autos _ _ _ s87Known _ s87Roots s87Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · unfold s87StockWords; decide +kernel
  · decide +kernel
  · simp only [s87Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def monoCircuit : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨.or, [5, 6]⟩, ⟨.or, [3, 4]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [1, 10]⟩, ⟨.or, [7, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.and, [1, 4]⟩, ⟨.and, [11, 12]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [16, 17]⟩, ⟨.or, [15, 18]⟩, ⟨.or, [14, 19]⟩, ⟨.or, [13, 20]⟩], 21⟩

end PEqualNP.Outside.L_meta_31291

open PEqualNP.Outside.L_meta_31291 in
theorem PEqualNP.Outside.L_meta_31291 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates out legal _ computes
  let target : (Fin 8 → Bool) → Bool := fun x => decide (∃ i < ([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 1, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 1, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
  let raw : List (BitVec 256) := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000, 0xffffffffffffffffffffffffffffffff00000000000000000000000000000000]
  let goal : BitVec 256 := 0xfffffffffffffffffffffffffffefffcfffffffffffefffcfffefffceeeeaa00
  have root : Lower (fullMask 256) (raw.map BitVec.toNat) goal.toNat 14 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s87Stock
  have fan : ∀ g ∈ gates, g.op ∈ ({.and, .or, .not} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    exact legal g hg
  have hit : PEqualNP.MetaComplexity.HasCircuitSize 8 target gates.length :=
    ⟨⟨gates, out⟩, fan, Nat.le_refl _, computes⟩
  have size := hcsLower raw goal 14 target (by decide +kernel) (by decide +kernel) root _ hit
  have monoEval : ∀ x, monoCircuit.eval (List.ofFn x) = target x := by
    intro x
    have clean : PEqualNP.MetaComplexity.FanInTwo monoCircuit := by
      intro gate member
      simp only [monoCircuit, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    exact hcsWitnessEval raw goal monoCircuit target clean (by decide +kernel) (by decide +kernel) (by decide +kernel) x
  refine ⟨monoCircuit.gates, monoCircuit.output, ?_, ?_, monoEval⟩
  · intro gate member
    simp only [monoCircuit, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact Nat.le_trans (by decide +kernel : monoCircuit.gates.length ≤ 14) size

