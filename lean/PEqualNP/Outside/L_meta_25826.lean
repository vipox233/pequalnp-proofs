import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25826

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

def Dominates (mask target better worse : Nat) : Prop :=
  ∀ i, mask.testBit i = true →
    worse.testBit i = target.testBit i → better.testBit i = target.testBit i

def dominanceB (mask target better worse : Nat) : Bool :=
  (((worse ^^^ target) ^^^ mask) &&& (better ^^^ target) &&& mask) == 0

theorem dominanceB_spec {mask target better worse : Nat} :
    dominanceB mask target better worse = true ↔ Dominates mask target better worse := by
  rw [show dominanceB mask target better worse = true ↔
       (((worse ^^^ target) ^^^ mask) &&& (better ^^^ target) &&& mask) = 0 by simp [dominanceB]]
  constructor
  · intro hz i mi wi
    have bit := congrArg (fun n : Nat => n.testBit i) hz
    simp only [Nat.testBit_xor, Nat.testBit_and, Nat.zero_testBit] at bit
    cases ti : target.testBit i <;> cases bi : better.testBit i <;> simp_all
  · intro dom
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_xor, Nat.testBit_and, Nat.zero_testBit]
    cases mi : mask.testBit i
    · simp
    cases wi : worse.testBit i <;> cases ti : target.testBit i <;>
      cases bi : better.testBit i <;> simp_all [Dominates]

theorem dominanceRefl (mask target word : Nat) : Dominates mask target word word :=
  fun _ _ h => h

theorem dominanceTrans {mask target a b c : Nat}
    (ab : Dominates mask target a b) (bc : Dominates mask target b c) :
    Dominates mask target a c :=
  fun i hi hc => ab i hi (bc i hi hc)

theorem dominanceBin {mask target a b c d : Nat} (op : Bool)
    (ac : Dominates mask target a c) (bd : Dominates mask target b d) :
    Dominates mask target (binWord op a b) (binWord op c d) := by
  intro i mi matchBit
  have h₁ := ac i mi
  have h₂ := bd i mi
  cases op <;> simp only [binWord, Bool.false_eq_true, ite_true, ite_false,
    Nat.testBit_and, Nat.testBit_or] at matchBit ⊢ <;>
    cases ht : target.testBit i <;> cases ha : a.testBit i <;> cases hb : b.testBit i <;>
    cases hc : c.testBit i <;> cases hd : d.testBit i <;> simp_all

theorem dominanceTarget {mask target word : Nat} (gw : Masked mask word)
    (gt : Masked mask target) (h : Dominates mask target word target) :
    word = target := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hm : mask.testBit i = true
  · exact h i hm rfl
  · have hw := congrArg (fun n : Nat => n.testBit i) gw
    have ht := congrArg (fun n : Nat => n.testBit i) gt
    simp_all [Nat.testBit_and]

def MonoGate (mask : Nat) (bank : List Nat) (out : Nat) : Prop :=
  ∃ a b, AvailableWord mask bank a ∧ AvailableWord mask bank b ∧
    (out = a &&& b ∨ out = a ||| b)

def MonoBuilds (mask : Nat) (bank : List Nat) : List Nat → Prop
  | [] => True
  | w :: ws => MonoGate mask bank w ∧ MonoBuilds mask (w :: bank) ws

def MonoLower (mask : Nat) (bank : List Nat) (target : Nat) (minimum : Nat) : Prop :=
  ∀ values, MonoBuilds mask bank values →
    AvailableWord mask (values ++ bank) target → minimum ≤ values.length

def DomPool (mask target : Nat) (bank source : List Nat) : Prop :=
  ∀ w, AvailableWord mask source w →
    ∃ d, AvailableWord mask bank d ∧ Dominates mask target d w

theorem domPoolCons {mask target w d : Nat} {bank source : List Nat}
    (supply : DomPool mask target bank source)
    (av : AvailableWord mask bank d) (dom : Dominates mask target d w) :
    DomPool mask target bank (w :: source) := by
  intro v hv
  rcases hv with eq | eq | hv
  · subst v; exact ⟨0, Or.inl rfl, dominanceRefl mask target 0⟩
  · subst v; exact ⟨mask, Or.inr (Or.inl rfl), dominanceRefl mask target mask⟩
  · rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨d, av, dom⟩
    · exact supply _ (Or.inr (Or.inr hv))

theorem dominanceSkip {mask target w d : Nat} {bank : List Nat}
    (av : AvailableWord mask bank d) (dom : Dominates mask target d w) :
    DomPool mask target bank (w :: bank) :=
  domPoolCons (fun _ h => ⟨_, h, dominanceRefl mask target _⟩) av dom

def DomBuilds (mask target : Nat) (bank : List Nat) : List Nat → Prop
  | [] => True
  | w :: ws => MonoGate mask bank w ∧
    (∀ d, AvailableWord mask bank d → ¬ Dominates mask target d w) ∧
    DomBuilds mask target (w :: bank) ws

theorem normalizeDominance {mask target : Nat} (gt : Masked mask target)
    {original bank values : List Nat} (build : MonoBuilds mask original values)
    (supply : DomPool mask target bank original)
    (bounded : ∀ w ∈ bank, Masked mask w)
    (hit : AvailableWord mask (values ++ original) target) :
    ∃ normalized, normalized.length ≤ values.length ∧
      DomBuilds mask target bank normalized ∧ AvailableWord mask (normalized ++ bank) target := by
  classical
  induction values generalizing original bank with
  | nil =>
    obtain ⟨d, av, dominates⟩ := supply target hit
    have eq := dominanceTarget (maskedAvailable bounded av) gt dominates
    exact ⟨[], Nat.le_refl _, trivial, eq ▸ av⟩
  | cons w ws ih =>
    have hit' : AvailableWord mask (ws ++ w :: original) target := by
      simpa [AvailableWord, List.mem_append, List.mem_cons, or_assoc, or_left_comm] using hit
    obtain ⟨a, b, ha, hb, gate⟩ := build.1
    obtain ⟨a', avA, domA⟩ := supply a ha
    obtain ⟨b', avB, domB⟩ := supply b hb
    have simulate (op : Bool) (wEq : w = binWord op a b) :
        ∃ normalized, normalized.length ≤ (w :: ws).length ∧
          DomBuilds mask target bank normalized ∧ AvailableWord mask (normalized ++ bank) target := by
      let v := binWord op a' b'
      have vd : Dominates mask target v w := wEq ▸ dominanceBin op domA domB
      have vg : MonoGate mask bank v := ⟨a', b', avA, avB, by cases op <;> simp [v, binWord]⟩
      by_cases redundant : ∃ d, AvailableWord mask bank d ∧ Dominates mask target d v
      · obtain ⟨d, av, dv⟩ := redundant
        obtain ⟨ys, len, good, out⟩ := ih build.2 (domPoolCons supply av (dominanceTrans dv vd)) bounded hit'
        exact ⟨ys, by simp only [List.length_cons]; omega, good, out⟩
      · have grow : DomPool mask target (v :: bank) original := by
          intro x hx
          obtain ⟨d, av, dx⟩ := supply x hx
          exact ⟨d, availableWeaken (fun _ hm => Or.inr (Or.inr (List.mem_cons_of_mem _ hm))) av, dx⟩
        have mb : ∀ x ∈ v :: bank, Masked mask x := by
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact maskedGate bounded (Or.inr vg)
          · exact bounded _ hx
        obtain ⟨ys, len, good, out⟩ :=
          ih build.2 (domPoolCons grow (Or.inr (Or.inr List.mem_cons_self)) vd) mb hit'
        refine ⟨v :: ys, by simp [len], ⟨vg, fun d av dv => redundant ⟨d, av, dv⟩, good⟩, ?_⟩
        simpa [AvailableWord, List.mem_append, List.mem_cons, or_assoc, or_left_comm] using out
    rcases gate with h | h
    · exact simulate false h
    · exact simulate true h

def DominanceRule (enabled : Bool) (mask target : Nat) (stock : List Nat)
    (S : Finset Nat) (w : Nat) : Prop :=
  enabled = true → ∀ x, (x ∈ S ∨ AvailableWord mask stock x) → ¬ Dominates mask target x w

def MonoPlan (enabled : Bool) (mask target : Nat) (stock : List Nat) :
    Nat → Finset Nat → Prop
  | 0, S => S = {target} ∧ properWord mask target
  | k + 1, S => ∃ (U : Finset Nat) (a b : Nat) (op : Bool),
      S = insert a (insert b U) ∧ properWord mask a ∧ properWord mask b ∧ a ≠ b ∧
      binWord op a b ∉ S ∧ binWord op a b ∉ stock ∧ DominanceRule enabled mask target stock S (binWord op a b) ∧
      MonoPlan enabled mask target stock k (insert (binWord op a b) U)

theorem monoPlanLive {enabled : Bool} {stock : List Nat} {k : Nat} {S : Finset Nat}
    (run : MonoPlan enabled mask target stock k S) : LiveWord mask target k 0 S := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hp⟩ := run
    exact LiveWord.stop hp
  | succ k ih =>
    obtain ⟨U, a, b, op, rfl, pa, pb, ab, fresh, _, _, tail⟩ := run
    exact LiveWord.binary pa pb ab fresh (ih tail)

def AdmissibleBuilds (enabled : Bool) (mask target : Nat) (bank : List Nat) : List Nat → Prop
  | [] => True
  | w :: ws => MonoGate mask bank w ∧
    (enabled = true → ∀ d, AvailableWord mask bank d → ¬ Dominates mask target d w) ∧
    AdmissibleBuilds enabled mask target (w :: bank) ws

theorem monoAdmissible {mask : Nat} {bank values : List Nat}
    (build : MonoBuilds mask bank values) : AdmissibleBuilds false mask target bank values := by
  induction values generalizing bank with
  | nil => trivial
  | cons w ws ih => exact ⟨build.1, by simp, ih build.2⟩

theorem domAdmissible {mask : Nat} {bank values : List Nat}
    (build : DomBuilds mask target bank values) : AdmissibleBuilds true mask target bank values := by
  induction values generalizing bank with
  | nil => trivial
  | cons w ws ih => exact ⟨build.1, fun _ => build.2.1, ih build.2.2⟩

theorem extractMonoPlan {enabled : Bool} {stock bank values : List Nat}
    (stockSub : ∀ w ∈ stock, w ∈ bank)
    (masked : ∀ w ∈ bank, Masked mask w)
    (build : AdmissibleBuilds enabled mask target bank values)
    (hit : AvailableWord mask (values ++ bank) target) (goal : properWord mask target) :
    ∃ k S, k ≤ values.length ∧ MonoPlan enabled mask target stock k S ∧ ∀ w ∈ S, w ∈ bank := by
  have mem := (hit.resolve_left goal.1).resolve_left goal.2
  induction values generalizing bank with
  | nil => exact ⟨0, {target}, Nat.zero_le _, ⟨rfl, goal⟩, by simpa using mem⟩
  | cons w ws ih =>
    have sub : ∀ v ∈ stock, v ∈ w :: bank := fun v hv => List.mem_cons_of_mem _ (stockSub v hv)
    have masked' : ∀ v ∈ w :: bank, Masked mask v := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact maskedGate masked (Or.inr build.1)
      · exact masked _ hv
    have mem' : target ∈ ws ++ w :: bank := by
      simpa [List.mem_append, List.mem_cons, or_assoc, or_left_comm] using mem
    obtain ⟨k, S, hk, plan, hs⟩ := ih sub masked' build.2.2 (Or.inr (Or.inr mem')) mem'
    have dropped (h : w ∉ S ∨ w ∈ bank) : ∀ v ∈ S, v ∈ bank := by
      intro v hv
      rcases List.mem_cons.mp (hs v hv) with rfl | hv'
      · exact h.resolve_left (fun hn => hn hv)
      · exact hv'
    by_cases used : w ∈ S
    swap
    · exact ⟨k, S, by simp only [List.length_cons]; omega, plan, dropped (Or.inl used)⟩
    by_cases old : w ∈ bank
    · exact ⟨k, S, by simp only [List.length_cons]; omega, plan, dropped (Or.inr old)⟩
    have proper := liveWordProper (monoPlanLive plan) w used
    have binary : binaryWitness mask bank w := by
      obtain ⟨a, b, ha, hb, h | h⟩ := build.1
      · rw [h]
        refine (classifyBinary masked false ha hb).resolve_left ?_
        intro hr
        exact ((hr.resolve_left (by simpa only [binWord, Bool.false_eq_true, ite_false, ite_true, ← h] using old)) (by simpa only [binWord, Bool.false_eq_true, ite_false, ite_true, ← h] using proper))
      · rw [h]
        refine (classifyBinary masked true ha hb).resolve_left ?_
        intro hr
        exact ((hr.resolve_left (by simpa only [binWord, Bool.false_eq_true, ite_false, ite_true, ← h] using old)) (by simpa only [binWord, Bool.false_eq_true, ite_false, ite_true, ← h] using proper))
    obtain ⟨op, a, b, ha, hb, pa, pb, ab, rfl⟩ := binary
    let v := binWord op a b
    let U := S.erase v
    have bankU : ∀ x ∈ U, x ∈ bank := by
      intro x hx
      obtain ⟨ne, hx⟩ := Finset.mem_erase.mp hx
      exact (List.mem_cons.mp (hs x hx)).resolve_left ne
    have bankNew : ∀ x ∈ insert a (insert b U), x ∈ bank := by simpa using And.intro ha (And.intro hb bankU)
    have rule : DominanceRule enabled mask target stock (insert a (insert b U)) v := by
      intro on d hd
      apply build.2.1 on d
      rcases hd with hd | hd
      · exact Or.inr (Or.inr (bankNew d hd))
      · exact availableWeaken (fun y hy => Or.inr (Or.inr (stockSub y hy))) hd
    refine ⟨k+1, _, by simp only [List.length_cons]; omega,
      ⟨U,a,b,op,rfl,pa,pb,ab,fun h => old (bankNew _ h),fun h => old (stockSub _ h),rule,?_⟩, bankNew⟩
    simpa [U, v, Finset.insert_erase used] using plan

theorem keepFilterEq {S U : Finset Nat} {a b : Nat} (ab : a ≠ b)
    (eq : S = insert a (insert b U)) :
    S.filter (fun x => (decide (a ∈ U) = true ∨ x ≠ a) ∧
      (decide (b ∈ U) = true ∨ x ≠ b)) = U := by
  ext x
  rw [Finset.mem_filter, eq]
  by_cases ha : x = a
  · subst x; simp [ab]
  by_cases hb : x = b
  · subst x; simp [ab.symm]
  simp [ha, hb]

theorem monoPlanWeaken {enabled : Bool} {stock : List Nat} {k : Nat} {S : Finset Nat}
    (h : MonoPlan enabled mask target stock k S) :
    MonoPlan false mask target stock k S := by
  induction k generalizing S with
  | zero => exact h
  | succ k ih =>
    obtain ⟨U,a,b,op,eq,pa,pb,ab,fresh,old,_,tail⟩ := h
    exact ⟨U,a,b,op,eq,pa,pb,ab,fresh,old,by simp [DominanceRule],ih tail⟩

theorem monoLowerWeaken {mask target minimum : Nat} {old new : List Nat}
    (lower : MonoLower mask old target minimum) (supply : ∀ w ∈ new, AvailableWord mask old w) :
    MonoLower mask new target minimum := by
  intro values build hit
  apply lower values
  · clear hit lower
    induction values generalizing new old with
    | nil => trivial
    | cons v vs ih =>
      obtain ⟨a,b,ha,hb,g⟩ := build.1
      refine ⟨⟨a,b,availableWeaken supply ha,availableWeaken supply hb,g⟩, ih ?_ build.2⟩
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact Or.inr (Or.inr List.mem_cons_self)
      · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)
  · apply availableWeaken _ hit
    intro w hw
    rcases List.mem_append.mp hw with hv | hn
    · exact Or.inr (Or.inr (List.mem_append_left _ hv))
    · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_append_right _ hx))) (supply _ hn)

namespace PackedRect

def domN (w d : ℕ) : Bool :=
  Nat.beq (Nat.land (Nat.land w 4095) (Nat.sub 16777215 d)) 0 &&
  Nat.beq (Nat.land (Nat.land d (Nat.sub 16777215 w)) 16773120) 0

def blk (m : Bool) (w d : ℕ) : Bool := cond m (domN w d) (Nat.beq w d)

def base10 : List ℕ :=
  [113184, 430348, 902208, 3227782, 5521457, 5689661, 8532035, 11083800, 13501056, 15731968]

def base12 : List ℕ := 0 :: 16777215 :: base10

theorem land_compl (w : ℕ) : w &&& (16777215 - w) = 0 := by
  rcases lt_or_ge w (2 ^ 24) with h | h
  · apply Nat.eq_of_testBit_eq
    intro i
    have e : 16777215 - w = 2 ^ 24 - (w + 1) := by omega
    rw [e, Nat.testBit_and, Nat.testBit_two_pow_sub_succ h]
    cases w.testBit i <;> simp
  · have e : 16777215 - w = 0 := by omega
    simp [e]

theorem domN_refl (w : ℕ) : domN w w = true := by
  have h := land_compl w
  have h1 : Nat.land (Nat.land w 4095) (Nat.sub 16777215 w) = 0 := by
    show (w &&& 4095) &&& (16777215 - w) = 0
    rw [Nat.and_right_comm, h]; simp
  have h2 : Nat.land (Nat.land w (Nat.sub 16777215 w)) 16773120 = 0 := by
    show (w &&& (16777215 - w)) &&& 16773120 = 0
    rw [h]; simp
  unfold domN
  rw [h1, h2]
  rfl

theorem blk_refl (m : Bool) (w : ℕ) : blk m w w = true := by
  cases m
  · simp [blk]
  · simp [blk, domN_refl]


def Reach (m : Bool) : Finset Nat → Nat → Prop
  | D, 0 => D = {4095}
  | D, k + 1 => D = {4095} ∨ ∃ (u v w : Nat) (ka kb : Bool),
    u ∈ D ∧ v ∈ D ∧ (w = u &&& v ∨ w = u ||| v) ∧
    (∀ d ∈ D, blk m w d = false) ∧ True ∧
    Reach m (insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k

theorem Reach.ind {m : Bool} {P : ∀ D k, Reach m D k → Prop}
    (done : ∀ k, P {4095} k (by cases k <;> first | rfl | exact Or.inl rfl))
    (step : ∀ D k u v w (ka kb : Bool) (hu : u ∈ D) (hv : v ∈ D)
      (hw : w = u &&& v ∨ w = u ||| v) (hd : ∀ d ∈ D, blk m w d = false), True →
      (tail : Reach m (insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k) →
      P (insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) k tail →
      P D (k + 1) (Or.inr ⟨u,v,w,ka,kb,hu,hv,hw,hd,trivial,tail⟩))
    {D k} (h : Reach m D k) : P D k h := by
  induction k generalizing D with
  | zero =>
    change D = {4095} at h
    subst D
    exact done 0
  | succ k ih =>
    rcases h with he | ⟨u, v, w, ka, kb, hu, hv, gate, hd, hb, tail⟩
    · subst D
      exact done (k + 1)
    · exact step D k u v w ka kb hu hv gate hd hb tail (ih tail)

theorem Reach.card {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) : D.card ≤ k + 1 := by
  induction h using Reach.ind with
  | done k => simp
  | step D k u v w ka kb hu hv hw hd hb _ ih =>
    have hwD : w ∉ D := fun hm => by
      have := hd w hm
      rw [blk_refl] at this
      exact Bool.noConfusion this
    have hwF : w ∉ D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)) :=
      fun hm => hwD (Finset.mem_of_mem_filter _ hm)
    rw [Finset.card_insert_of_notMem hwF] at ih
    have hsub : D ⊆ insert u (insert v
        (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))) := by
      intro x hx
      by_cases h1 : x = u
      · simp [h1]
      by_cases h2 : x = v
      · simp [h2]
      simp [hx, h1, h2]
    have h2 := Finset.card_le_card hsub
    have h3 := Finset.card_insert_le u (insert v
        (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))))
    have h4 := Finset.card_insert_le v
        (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))
    omega

theorem tb4095 (i : ℕ) : (4095 : ℕ).testBit i = decide (i < 12) := by
  have e : (4095 : ℕ) = 2 ^ 12 - 1 := by norm_num
  rw [e, Nat.testBit_two_pow_sub_one]

theorem Reach.sep {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) (e i : ℕ) (he : e < 12)
    (hi : 12 ≤ i) : ∃ w ∈ D, w.testBit e = true ∧ w.testBit i = false := by
  induction h using Reach.ind with
  | done k =>
    refine ⟨4095, by simp, ?_, ?_⟩
    · rw [tb4095]; simpa using he
    · rw [tb4095]; simpa using hi
  | step D k u v w ka kb hu hv hw hd hb _ ih =>
    obtain ⟨x, hx, h1, h2⟩ := ih
    rcases Finset.mem_insert.mp hx with hxw | hx
    · subst hxw
      rcases hw with hw | hw
      · subst hw
        rw [Nat.testBit_and] at h1 h2
        cases hum : u.testBit i
        · exact ⟨u, hu, by simp_all, hum⟩
        · exact ⟨v, hv, by simp_all, by simp_all⟩
      · subst hw
        rw [Nat.testBit_or] at h1 h2
        cases hue : u.testBit e
        · exact ⟨v, hv, by simp_all, by simp_all⟩
        · exact ⟨u, hu, hue, by simp_all⟩
    · exact ⟨x, Finset.mem_of_mem_filter _ hx, h1, h2⟩

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

theorem sep_bit {m : Bool} {D : Finset ℕ} {k : ℕ} (hR : Reach m D k) (p : ℕ) (hp : p < 144) :
    ∃ x ∈ D, (rectW x).testBit p = true := by
  obtain ⟨x, hx, h1, h2⟩ := hR.sep (p / 12) (12 + p % 12) (by omega) (by omega)
  refine ⟨x, hx, ?_⟩
  have := rectW_tb x (p / 12) (p % 12) (by omega) (Nat.mod_lt _ (by norm_num)) h1 h2
  rwa [Nat.div_add_mod] at this

def full : ℕ := 22300745198530623141535718272648361505980415

theorem full_eq : full = 2 ^ 144 - 1 := by norm_num [full]

def covR (c : ℕ) : Bool := Nat.beq (Nat.land c full) full

theorem covR_of (c : ℕ) (h : ∀ p, p < 144 → c.testBit p = true) : covR c = true := by
  have e : Nat.land c full = full := by
    show c &&& full = full
    rw [full_eq]
    apply Nat.eq_of_testBit_eq
    intro p
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
    by_cases hp : p < 144
    · simp [hp, h p hp]
    · simp [hp]
  unfold covR
  rw [e]
  exact Nat.beq_refl _

def orR : List ℕ → ℕ
  | [] => 0
  | x :: l => Nat.lor (rectW x) (orR l)

theorem orR_tb (p : ℕ) : ∀ l : List ℕ, ∀ x ∈ l, (rectW x).testBit p = true →
    (orR l).testBit p = true := by
  intro l
  induction l with
  | nil => intro x hx; simp at hx
  | cons a l ih =>
    intro x hx h
    show (rectW a ||| orR l).testBit p = true
    rw [Nat.testBit_or]
    rcases List.mem_cons.mp hx with hxa | hx
    · rw [← hxa, h]; rfl
    · rw [ih x hx h]; simp

theorem cover_sound {m : Bool} {l : List ℕ} {k : ℕ} (h : covR (orR l) = false) :
    ¬ Reach m l.toFinset k := by
  intro hR
  have : covR (orR l) = true := by
    apply covR_of
    intro p hp
    obtain ⟨x, hx, hb⟩ := sep_bit hR p hp
    exact orR_tb p l x (List.mem_toFinset.mp hx) hb
  rw [h] at this
  exact Bool.noConfusion this
def bor (a b : Bool) : Bool := @Bool.rec (fun _ => Bool) b true a
def band (a b : Bool) : Bool := @Bool.rec (fun _ => Bool) false b a
def bnot (a : Bool) : Bool := @Bool.rec (fun _ => Bool) true false a

theorem bor_eq (a b : Bool) : bor a b = (a || b) := by cases a <;> rfl
theorem band_eq (a b : Bool) : band a b = (a && b) := by cases a <;> rfl
theorem bnot_eq (a : Bool) : bnot a = !a := by cases a <;> rfl
def tb' (w e : ℕ) : Bool := bnot (Nat.beq (Nat.land (Nat.shiftRight w e) 1) 0)

theorem tb'_eq (w e : ℕ) : tb' w e = tb w e := by
  unfold tb' tb; rw [bnot_eq]

def rect' (x J n : ℕ) : ℕ :=
  @Nat.rec (fun _ => ℕ) 0
    (fun e ih => Nat.lor (@Bool.rec (fun _ => ℕ) 0 (Nat.shiftLeft J (Nat.mul 12 e)) (tb' x e)) ih) n

theorem rect'_eq (x J n : ℕ) : rect' x J n = rect x J n := by
  induction n with
  | zero => rfl
  | succ e ih =>
    show Nat.lor (@Bool.rec (fun _ => ℕ) 0 (Nat.shiftLeft J (Nat.mul 12 e)) (tb' x e)) (rect' x J e) =
      Nat.lor (cond (tb x e) (Nat.shiftLeft J (Nat.mul 12 e)) 0) (rect x J e)
    rw [ih, tb'_eq]
    cases tb x e <;> rfl

theorem rectTest (x J n q : Nat) (bounded : J < 4096) :
    (rect x J n).testBit q =
      (decide (q / 12 < n) && x.testBit (q / 12) && J.testBit (q % 12)) := by
  induction n with
  | zero => simp [rect]
  | succ n ih =>
    change ((cond (tb x n) (J <<< (12*n)) 0) ||| rect x J n).testBit q = _
    rw [Nat.testBit_or, ih, tb_eq]
    by_cases before : q / 12 < n
    · have start : ¬ 12*n ≤ q := by omega
      have next : q/12 < n+1 := by omega
      cases x.testBit n <;> simp [Nat.testBit_shiftLeft, start, before, next]
    by_cases lane : q / 12 = n
    · have start : 12*n ≤ q := by omega
      have off : q-12*n = q % 12 := by omega
      have next : q/12 < n+1 := by omega
      cases enabled : x.testBit n <;> simp [Nat.testBit_shiftLeft, start, off, before, next, lane, enabled]
    · have next : ¬ q/12 < n+1 := by omega
      have off : 12 ≤ q-12*n := by omega
      have beyond : J.testBit (q-12*n) = false := by
        apply Nat.testBit_lt_two_pow
        exact lt_of_lt_of_le bounded (Nat.pow_le_pow_right (by decide : 0 < 2) off)
      cases x.testBit n <;> simp [Nat.testBit_shiftLeft, before, next, beyond]

def rectScan (p : Nat → Bool) : Nat → Nat → Bool :=
  Nat.rec p (fun k prev s => prev s && prev (s + 2^k))

theorem rectScanAt {p : Nat → Bool} {k s i : Nat}
    (h : rectScan p k s = true) (lo : s ≤ i) (hi : i < s + 2^k) : p i = true := by
  induction k generalizing s with
  | zero =>
    have eq : i = s := by omega
    simpa [eq, rectScan] using h
  | succ k ih =>
    obtain ⟨left,right⟩ := Bool.and_eq_true_iff.mp h
    by_cases half : i < s + 2^k
    · exact ih left lo half
    · apply ih right (by omega)
      rw [Nat.pow_succ] at hi
      omega

def rectRowMask (p : Nat) : Nat :=
  let table := 0xfffffffffffffffffffff000ffffff000fffffffff000000fff000fffffffff000fff000fff000000ffffff000000000000fffffffff000ffffff000000fff000fff000fff000000000000ffffff000000fff000000000000fff000000000000
  (unpack table 48 (p &&& 15)) |||
    ((unpack table 48 ((p >>> 4) &&& 15)) <<< 48) |||
    ((unpack table 48 ((p >>> 8) &&& 15)) <<< 96)

def rectRepeat (J : Nat) : Nat := J * 0x1001001001001001001001001001001001

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem rectArithmeticCheck :
    rectScan (fun v => Nat.beq (rectRowMask v) (rect' v 4095 12) &&
      Nat.beq (rectRepeat v) (rect' 4095 v 12)) 12 0 = true := by
  decide +kernel

theorem rectArithmeticAt {i : Nat} (h : i < 4096) :
    rectRowMask i = rect i 4095 12 ∧ rectRepeat i = rect 4095 i 12 := by
  have line := rectScanAt rectArithmeticCheck (i := i) (Nat.zero_le _) (by simpa using h)
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp line
  exact ⟨(Nat.beq_eq.mp a).trans (rect'_eq ..), (Nat.beq_eq.mp b).trans (rect'_eq ..)⟩

def rectW' (x : Nat) : Nat :=
  let J := (x >>> 12) ^^^ 4095
  if Nat.blt J 4096 then rectRowMask (x % 4096) &&& rectRepeat J
  else rect' x J 12

theorem rectW'_eq (x : Nat) : rectW' x = rectW x := by
  unfold rectW' rectW
  let J := (x >>> 12) ^^^ 4095
  change (if Nat.blt J 4096 then rectRowMask (x % 4096) &&& rectRepeat J
    else rect' x J 12) = rect x J 12
  split
  · next good =>
    have small := Nat.blt_eq.mp good
    have modSmall : x % 4096 < 4096 := Nat.mod_lt _ (by decide)
    rw [(rectArithmeticAt modSmall).1, (rectArithmeticAt small).2]
    apply Nat.eq_of_testBit_eq
    intro q
    rw [Nat.testBit_and, rectTest _ _ _ _ (by decide), rectTest _ _ _ _ small,
      rectTest _ _ _ _ small, tb4095, tb4095]
    change (_ && (x % 2^12).testBit (q/12) && _ && _) = _
    rw [Nat.testBit_mod_two_pow]
    have modLt : q % 12 < 12 := Nat.mod_lt _ (by decide)
    simp only [modLt, decide_true, Bool.and_true]
    cases decide (q/12 < 12) <;> rfl
  · exact rect'_eq .. 

theorem ite_p {c : Prop} [Decidable c] (a b : ℕ) (h : c) : (if c then a else b) = a := by
  split
  · rfl
  · contradiction

theorem ite_n {c : Prop} [Decidable c] (a b : ℕ) (h : ¬ c) : (if c then a else b) = b := by
  split
  · contradiction
  · rfl

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

theorem kw_step (D D' : Finset ℕ) (u v w : ℕ) (c : ℕ → ℕ → Bool) (f : ℕ → ℕ → ℕ)
    (hu : u ∈ D) (hv : v ∈ D) (huv : u ≠ v) (huD : u ∉ D') (hvD : v ∉ D')
    (hsub : ∀ x ∈ D', x ≠ w → x ∈ D)
    (hf : ∀ e i, e < 12 → 12 ≤ i →
      f e i ∈ D' ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false)
    (hr : ∀ e i e' i', e < 12 → e' < 12 → 12 ≤ i → 12 ≤ i' → f e i = f e' i' → f e i' = f e i)
    (hcu : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = true →
      u.testBit e = true ∧ u.testBit i = false)
    (hcv : ∀ e i, w.testBit e = true → w.testBit i = false → c e i = false →
      v.testBit e = true ∧ v.testBit i = false)
    (hc : ∀ e i e' i', c e i = c e' i' → c e i' = c e i) :
    ∃ g : ℕ → ℕ → ℕ,
      (∀ e i, e < 12 → 12 ≤ i →
        g e i ∈ D ∧ (g e i).testBit e = true ∧ (g e i).testBit i = false) ∧
      (∀ e i e' i', e < 12 → e' < 12 → 12 ≤ i → 12 ≤ i' → g e i = g e' i' → g e i' = g e i) := by
  have hg : ∀ e i, e < 12 → 12 ≤ i → f e i = w →
      ((if f e i = w then (cond (c e i) u v) else f e i) = u ∧ c e i = true) ∨
      ((if f e i = w then (cond (c e i) u v) else f e i) = v ∧ c e i = false) := by
    intro e i _ _ h
    rw [ite_p _ _ (h)]
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
    · rw [ite_n _ _ (hw)]; exact ⟨hsub _ h1 hw, h2, h3⟩
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
        rw [ite_p _ _ (h3), ite_p _ _ (h1), hc e i e' i' hcc]
      · exfalso
        rw [ite_n _ _ (h2)] at heq'
        have hm := (hf e' i' he' hi').1
        rcases hg e i he hi h1 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, heq']; exact hm)
        · exact hvD (by rw [← hx, heq']; exact hm)
    · by_cases h2 : f e' i' = w
      · exfalso
        rw [ite_n _ _ (h1)] at heq'
        have hm := (hf e i he hi).1
        rcases hg e' i' he' hi' h2 with ⟨hx, _⟩ | ⟨hx, _⟩
        · exact huD (by rw [← hx, ← heq']; exact hm)
        · exact hvD (by rw [← hx, ← heq']; exact hm)
      · have h1n : (if f e i = w then (cond (c e i) u v) else f e i) = f e i := ite_n _ _ h1
        have h2n : (if f e' i' = w then (cond (c e' i') u v) else f e' i') = f e' i' := ite_n _ _ h2
        rw [h1n, h2n] at heq'
        have h3 := hr e i e' i' he he' hi hi' heq'
        have h3n : ¬ f e i' = w := by rw [h3]; exact h1
        rw [h1n, ite_n _ _ (h3n)]
        exact h3

theorem size_lb2 (D : Finset ℕ) (u v : ℕ) (ka kb : Bool) :
    D.card ≤ (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))).card +
      (cond ka 0 1 + cond kb 0 1) := by
  have hsub : D ⊆ (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) ∪
      ((cond ka ∅ {u}) ∪ (cond kb ∅ {v})) := by
    intro x hx
    by_cases h1 : x = u <;> by_cases h2 : x = v <;> cases ka <;> cases kb <;> simp_all
  have h1 := Finset.card_le_card hsub
  have h2 := Finset.card_union_le (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)))
    ((cond ka ∅ {u}) ∪ (cond kb ∅ {v}))
  have h3 := Finset.card_union_le (cond ka (∅ : Finset ℕ) {u}) (cond kb ∅ {v})
  have h4 : (cond ka (∅ : Finset ℕ) {u}).card = cond ka 0 1 := by cases ka <;> simp
  have h5 : (cond kb (∅ : Finset ℕ) {v}).card = cond kb 0 1 := by cases kb <;> simp
  omega

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

theorem Reach.kw {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) (ht : D.card = k + 1) :
    ∃ f : ℕ → ℕ → ℕ,
      (∀ e i, e < 12 → 12 ≤ i →
        f e i ∈ D ∧ (f e i).testBit e = true ∧ (f e i).testBit i = false) ∧
      (∀ e i e' i', e < 12 → e' < 12 → 12 ≤ i → 12 ≤ i' → f e i = f e' i' → f e i' = f e i) := by
  induction h using Reach.ind with
  | done k =>
    refine ⟨fun _ _ => 4095, ?_, ?_⟩
    · intro e i he hi
      refine ⟨by simp, ?_, ?_⟩
      · rw [tb4095]; simpa using he
      · rw [tb4095]; simpa using hi
    · intros; rfl
  | step D k u v w ka kb hu hv hw hd hb hR ih =>
    have hwD : w ∉ D := fun hm => by
      have := hd w hm
      rw [blk_refl] at this
      exact Bool.noConfusion this
    have hwu : w ≠ u := fun h => hwD (h ▸ hu)
    have hwv : w ≠ v := fun h => hwD (h ▸ hv)
    have huv : u ≠ v := by
      rintro rfl
      rcases hw with hw | hw
      · rw [Nat.and_self] at hw; exact hwu hw
      · rw [Nat.or_self] at hw; exact hwu hw
    have hwF : w ∉ D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)) :=
      fun hm => hwD (Finset.mem_of_mem_filter _ hm)
    have hkk : ka = false ∧ kb = false := by
      have h1 := hR.card
      rw [Finset.card_insert_of_notMem hwF] at h1
      have h2 := size_lb2 D u v ka kb
      generalize (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))).card = c at h1 h2
      cases ka <;> cases kb
      · exact ⟨rfl, rfl⟩
      · exfalso
        have h2' : D.card ≤ c + (1 + 0) := h2
        omega
      · exfalso
        have h2' : D.card ≤ c + (0 + 1) := h2
        omega
      · exfalso
        have h2' : D.card ≤ c + (0 + 0) := h2
        omega
    obtain ⟨rfl, rfl⟩ := hkk
    have h1 := hR.card
    rw [Finset.card_insert_of_notMem hwF] at h1
    have h2 : D.card ≤ (D.filter
        (fun x => (false = true ∨ x ≠ u) ∧ (false = true ∨ x ≠ v))).card + (1 + 1) :=
      size_lb2 D u v false false
    have hc : (insert w (D.filter
        (fun x => (false = true ∨ x ≠ u) ∧ (false = true ∨ x ≠ v)))).card = k + 1 := by
      rw [Finset.card_insert_of_notMem hwF]; omega
    obtain ⟨f, hf, hr⟩ := ih hc
    have huD : u ∉ insert w (D.filter
        (fun x => (false = true ∨ x ≠ u) ∧ (false = true ∨ x ≠ v))) := by
      intro hm
      rcases Finset.mem_insert.mp hm with h | h
      · exact hwu h.symm
      · have := (Finset.mem_filter.mp h).2.1
        simp at this
    have hvD : v ∉ insert w (D.filter
        (fun x => (false = true ∨ x ≠ u) ∧ (false = true ∨ x ≠ v))) := by
      intro hm
      rcases Finset.mem_insert.mp hm with h | h
      · exact hwv h.symm
      · have := (Finset.mem_filter.mp h).2.2
        simp at this
    have hsub : ∀ x ∈ insert w (D.filter
        (fun x => (false = true ∨ x ≠ u) ∧ (false = true ∨ x ≠ v))), x ≠ w → x ∈ D := by
      intro x hx hxw
      rcases Finset.mem_insert.mp hx with h | h
      · exact absurd h hxw
      · exact Finset.mem_of_mem_filter _ h
    rcases hw with rfl | rfl
    · exact kw_step D _ u v (u &&& v) (fun _ i => !(u.testBit i)) f hu hv huv huD hvD hsub hf hr
        (fun e i h1 h2 h3 => and_cu u v e i h1 h2 h3) (fun e i h1 h2 h3 => and_cv u v e i h1 h2 h3)
        (fun e i e' i' h => h.symm)
    · exact kw_step D _ u v (u ||| v) (fun e _ => u.testBit e) f hu hv huv huD hvD hsub hf hr
        (fun e i h1 h2 h3 => or_cu u v e i h1 h2 h3) (fun e i h1 h2 h3 => or_cv u v e i h1 h2 h3)
        (fun e i e' i' _ => rfl)

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

theorem orL_tb' (q : ℕ) : ∀ as : List ℕ, ∀ a ∈ as, a.testBit q = true →
    (orL as).testBit q = true := by
  intro as
  induction as with
  | nil => intro a ha; simp at ha
  | cons b l ih =>
    intro a ha h
    show (Nat.lor b (orL l)).testBit q = true
    rw [tb_lor]
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [h]; rfl
    · rw [ih a ha h]; simp

theorem Part.covR {zs : List ((ℕ → Prop) × ℕ)} (hP : Part zs) :
    covR (orL (zs.map Prod.snd)) = true := by
  apply covR_of
  intro q hq
  obtain ⟨z, hz, hzq⟩ := hP.cov q hq
  exact orL_tb' q _ z.2 (List.mem_map.mpr ⟨z, hz, rfl⟩) (hP.sub z hz q hzq)

theorem part_of_reach {m : Bool} {l : List ℕ} {k : ℕ} (hnd : l.Nodup) (hlen : l.length = k + 1)
    (hR : Reach m l.toFinset k) :
    ∃ zs : List ((ℕ → Prop) × ℕ), zs.map Prod.snd = l.map rectW ∧ Part zs := by
  have hc : l.toFinset.card = k + 1 := by rw [List.toFinset_card_of_nodup hnd, hlen]
  obtain ⟨f, hf, hr⟩ := hR.kw hc
  refine ⟨l.map (fun w => ((fun q => q < 144 ∧ f (q / 12) (12 + q % 12) = w), rectW w)), ?_, ?_⟩
  · rw [List.map_map]
    rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
      intro e i e' i' he hi he' hi' h1 h2
      have h1' : f ((12 * e + i) / 12) (12 + (12 * e + i) % 12) = w := h1.2
      have h2' : f ((12 * e' + i') / 12) (12 + (12 * e' + i') % 12) = w := h2.2
      have e1 : (12 * e + i) / 12 = e := by omega
      have e2 : (12 * e + i) % 12 = i := by omega
      have e3 : (12 * e' + i') / 12 = e' := by omega
      have e4 : (12 * e' + i') % 12 = i' := by omega
      have e5 : (12 * e + i') / 12 = e := by omega
      have e6 : (12 * e + i') % 12 = i' := by omega
      rw [e1, e2] at h1'
      rw [e3, e4] at h2'
      show 12 * e + i' < 144 ∧ f ((12 * e + i') / 12) (12 + (12 * e + i') % 12) = w
      rw [e5, e6]
      exact ⟨by omega, (hr e (12 + i) e' (12 + i') he he' (by omega) (by omega)
        (h1'.trans h2'.symm)).trans h1'⟩
    · intro z hz q hq
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
      exact hq.1
    · rw [List.pairwise_map]
      exact List.Pairwise.imp (fun hne q h1 h2 => hne (h1.2.symm.trans h2.2)) hnd
    · intro q hq
      have h := (hf (q / 12) (12 + q % 12) (by omega) (by omega)).1
      exact ⟨_, List.mem_map.mpr ⟨_, List.mem_toFinset.mp h, rfl⟩, hq, rfl⟩
    · intro z hz q hq
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp hz
      have hq1 : q < 144 := hq.1
      have hq2 : f (q / 12) (12 + q % 12) = w := hq.2
      have h := hf (q / 12) (12 + q % 12) (by omega) (by omega)
      rw [hq2] at h
      have h3 := rectW_tb w (q / 12) (q % 12) (by omega) (Nat.mod_lt _ (by norm_num)) h.2.1 h.2.2
      rwa [Nat.div_add_mod] at h3

theorem rectOK1_sound {m : Bool} {l : List ℕ} {k : ℕ} (hnd : l.Nodup) (hlen : l.length = k + 1)
    (hR : Reach m l.toFinset k) : rectOK1 l = true := by
  obtain ⟨zs, he, hP⟩ := part_of_reach hnd hlen hR
  unfold rectOK1
  rw [← he]
  exact avOK1_sound hP

def rectP1 (l : List ℕ) (k : ℕ) : Bool := !(Nat.beq l.length (Nat.succ k)) || rectOK1 l
def tw' (l : List ℕ) : ℕ → ℕ → ℕ :=
  @List.rec ℕ (fun _ => ℕ → ℕ → ℕ) (fun _ t => t)
    (fun a _ ih o t => ih (Nat.lor o a) (Nat.lor t (Nat.land o a))) l

theorem tw'_eq (l : List ℕ) : ∀ o t : ℕ, tw' l o t = tw l o t := by
  induction l with
  | nil => intro o t; rfl
  | cons a l ih =>
    intro o t
    show tw' l (Nat.lor o a) (Nat.lor t (Nat.land o a)) = tw l (Nat.lor o a) (Nat.lor t (Nat.land o a))
    exact ih _ _

def hullsOK' (t : ℕ) (l : List ℕ) : ℕ → Bool :=
  @List.rec ℕ (fun _ => ℕ → Bool) (fun _ => true)
    (fun a _ ih acc => (fun h => band (Nat.beq (Nat.land h a) h)
      (band (Nat.beq (Nat.land acc h) 0) (ih (Nat.lor acc h)))) (priv t a)) l

theorem hullsOK'_eq (t : ℕ) (l : List ℕ) : ∀ acc : ℕ, hullsOK' t l acc = hullsOK t l acc := by
  induction l with
  | nil => intro acc; rfl
  | cons a l ih =>
    intro acc
    show band (Nat.beq (Nat.land (priv t a) a) (priv t a))
      (band (Nat.beq (Nat.land acc (priv t a)) 0) (hullsOK' t l (Nat.lor acc (priv t a)))) =
      (Nat.beq (Nat.land (priv t a) a) (priv t a) &&
        (Nat.beq (Nat.land acc (priv t a)) 0 && hullsOK t l (Nat.lor acc (priv t a))))
    rw [ih, band_eq, band_eq]

def mapW' (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [] (fun x _ ih => rectW' x :: ih) l

theorem mapW'_eq (l : List ℕ) : mapW' l = l.map rectW := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    show rectW' x :: mapW' l = rectW x :: l.map rectW
    rw [ih, rectW'_eq]
def Pc (x e i : ℕ) : Prop := x.testBit e = true ∧ x.testBit i = false

def IsRect2 (S : ℕ → ℕ → Prop) : Prop := ∀ e i e' i' : ℕ, S e i → S e' i' → S e i'

theorem pc_rect (x : ℕ) : IsRect2 (Pc x) := fun _ _ _ _ h1 h2 => ⟨h1.1, h2.2⟩

def KS (D : Finset ℕ) (j : ℕ) (f : ℕ → ℕ → ℕ) (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ)
    (Pi : ℕ → ℕ → ℕ → Prop) : Prop :=
  (∀ e i, e < 12 → 12 ≤ i → f e i ∈ D ∧ env (f e i) e i) ∧
  (∀ x ∈ D, IsRect2 (env x)) ∧
  (∀ x ∈ D, ∀ e i, env x e i → Pc x e i) ∧
  (∀ x ∈ D, ∀ y ∈ D, x ≠ y → c x = c y → ∀ e i, env x e i → env y e i → False) ∧
  (∀ x ∈ D, 1 ≤ c x → ∀ e i, env x e i → Pi (c x) e i) ∧
  (∀ n, IsRect2 (Pi n)) ∧
  (∀ n e i, 1 ≤ n → Pi n e i → ∃ y ∈ D, 1 ≤ c y ∧ c y ≤ n ∧ Pc y e i) ∧
  (∀ x ∈ D, c x ≤ j)

theorem KS.own {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ e i, e < 12 → 12 ≤ i → f e i ∈ D ∧ env (f e i) e i := h.1

theorem KS.envR {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ x ∈ D, IsRect2 (env x) := h.2.1

theorem KS.envP {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ x ∈ D, ∀ e i, env x e i → Pc x e i := h.2.2.1

theorem KS.s1 {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ x ∈ D, ∀ y ∈ D, x ≠ y → c x = c y → ∀ e i, env x e i → env y e i → False := h.2.2.2.1

theorem KS.s2 {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ x ∈ D, 1 ≤ c x → ∀ e i, env x e i → Pi (c x) e i := h.2.2.2.2.1

theorem KS.piR {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ n, IsRect2 (Pi n) := h.2.2.2.2.2.1

theorem KS.s3 {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ n e i, 1 ≤ n → Pi n e i → ∃ y ∈ D, 1 ≤ c y ∧ c y ≤ n ∧ Pc y e i := h.2.2.2.2.2.2.1

theorem KS.lab {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) :
    ∀ x ∈ D, c x ≤ j := h.2.2.2.2.2.2.2


theorem ks_done : KS {4095} 0 (fun _ _ => 4095) (fun _ e i => Pc 4095 e i) (fun _ => 0)
    (fun _ _ _ => False) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e i he hi
    refine ⟨by simp, ?_, ?_⟩
    · rw [tb4095]; simpa using he
    · rw [tb4095]; simpa using hi
  · intro x _; exact pc_rect 4095
  · intro x hx e i h
    rw [Finset.mem_singleton.mp hx]; exact h
  · intro x hx y hy hxy
    exact absurd ((Finset.mem_singleton.mp hx).trans (Finset.mem_singleton.mp hy).symm) hxy
  · intro x _ h; simp at h
  · intro n e i e' i' h; exact h.elim
  · intro n e i _ h; exact h.elim
  · intro x _; exact le_rfl

def shiftL (c : ℕ → ℕ) (x y : ℕ) : ℕ := if y = x then 1 else if c y = 0 then 0 else c y + 1

theorem shiftL_self (c : ℕ → ℕ) (x : ℕ) : shiftL c x x = 1 := by
  unfold shiftL; exact ite_p _ _ rfl

theorem shiftL_ne (c : ℕ → ℕ) (x y : ℕ) (h : y ≠ x) :
    (c y = 0 ∧ shiftL c x y = 0) ∨ (1 ≤ c y ∧ shiftL c x y = c y + 1) := by
  unfold shiftL
  rw [ite_n _ _ h]
  by_cases h0 : c y = 0
  · rw [ite_p _ _ h0]; exact Or.inl ⟨h0, rfl⟩
  · rw [ite_n _ _ h0]; exact Or.inr ⟨by omega, rfl⟩

theorem KS.promote {D : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D j f env c Pi) (x : ℕ) (hxD : x ∈ D) :
    KS D (j + 1) f (fun y e i => (y = x ∧ Pc x e i) ∨ (y ≠ x ∧ env y e i)) (shiftL c x)
      (fun n e i => (n = 1 ∧ Pc x e i) ∨ (2 ≤ n ∧ Pi (n - 1) e i)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1, h2⟩ := h.own e i he hi
    refine ⟨h1, ?_⟩
    by_cases hx : f e i = x
    · exact Or.inl ⟨hx, hx ▸ h.envP _ h1 e i h2⟩
    · exact Or.inr ⟨hx, h2⟩
  · intro y hy e i e' i' h1 h2
    rcases h1 with ⟨hx, h1⟩ | ⟨hx, h1⟩ <;> rcases h2 with ⟨hx', h2⟩ | ⟨hx', h2⟩
    · exact Or.inl ⟨hx, pc_rect x e i e' i' h1 h2⟩
    · exact absurd hx hx'
    · exact absurd hx' hx
    · exact Or.inr ⟨hx, h.envR y hy e i e' i' h1 h2⟩
  · intro y hy e i h1
    rcases h1 with ⟨hx, h1⟩ | ⟨hx, h1⟩
    · rw [hx]; exact h1
    · exact h.envP y hy e i h1
  · intro y hy z hz hyz hc e i h1 h2
    by_cases hyx : y = x
    · have hzx : z ≠ x := fun hh => hyz (hyx.trans hh.symm)
      rw [hyx, shiftL_self] at hc
      rcases shiftL_ne c x z hzx with ⟨_, h3⟩ | ⟨_, h3⟩ <;> omega
    · by_cases hzx : z = x
      · rw [hzx, shiftL_self] at hc
        rcases shiftL_ne c x y hyx with ⟨_, h3⟩ | ⟨_, h3⟩ <;> omega
      · have hcc : c y = c z := by
          rcases shiftL_ne c x y hyx with ⟨_, h3⟩ | ⟨_, h3⟩ <;>
            rcases shiftL_ne c x z hzx with ⟨_, h4⟩ | ⟨_, h4⟩ <;> omega
        rcases h1 with ⟨hx, _⟩ | ⟨_, h1⟩
        · exact hyx hx
        · rcases h2 with ⟨hx, _⟩ | ⟨_, h2⟩
          · exact hzx hx
          · exact h.s1 y hy z hz hyz hcc e i h1 h2
  · intro y hy hc e i h1
    rcases h1 with ⟨hx, h1⟩ | ⟨hx, h1⟩
    · rw [hx, shiftL_self]; exact Or.inl ⟨rfl, h1⟩
    · rcases shiftL_ne c x y hx with ⟨_, h3⟩ | ⟨h4, h3⟩
      · omega
      · rw [h3]
        refine Or.inr ⟨by omega, ?_⟩
        rw [Nat.add_sub_cancel]
        exact h.s2 y hy h4 e i h1
  · intro n e i e' i' h1 h2
    rcases h1 with ⟨hn, h1⟩ | ⟨hn, h1⟩ <;> rcases h2 with ⟨hn', h2⟩ | ⟨hn', h2⟩
    · exact Or.inl ⟨hn, pc_rect x e i e' i' h1 h2⟩
    · omega
    · omega
    · exact Or.inr ⟨hn, h.piR _ e i e' i' h1 h2⟩
  · intro n e i hn h1
    rcases h1 with ⟨hn1, h1⟩ | ⟨hn2, h1⟩
    · exact ⟨x, hxD, by rw [shiftL_self], by rw [shiftL_self]; omega, h1⟩
    · obtain ⟨y, hy, h3, h4, h5⟩ := h.s3 (n - 1) e i (by omega) h1
      by_cases hyx : y = x
      · exact ⟨y, hy, by rw [hyx, shiftL_self], by rw [hyx, shiftL_self]; omega, h5⟩
      · rcases shiftL_ne c x y hyx with ⟨_, h6⟩ | ⟨_, h6⟩
        · omega
        · exact ⟨y, hy, by omega, by omega, h5⟩
  · intro y hy
    have := h.lab y hy
    by_cases hyx : y = x
    · rw [hyx, shiftL_self]; omega
    · rcases shiftL_ne c x y hyx with ⟨_, h6⟩ | ⟨_, h6⟩ <;> omega

def Prom (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (w x : ℕ) : Prop :=
  (∀ e i, Pc x e i → env x e i) ∧ 1 ≤ c x ∧ (1 ≤ c w → c x ≤ c w)

theorem prom_self (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (w x : ℕ) :
    Prom (fun y e i => (y = x ∧ Pc x e i) ∨ (y ≠ x ∧ env y e i)) (shiftL c x) w x := by
  refine ⟨fun e i h => Or.inl ⟨rfl, h⟩, by rw [shiftL_self], fun h => by rw [shiftL_self]; exact h⟩

theorem prom_other (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (w x y : ℕ) (hyx : y ≠ x) (hwx : w ≠ x)
    (h : Prom env c w y) :
    Prom (fun y e i => (y = x ∧ Pc x e i) ∨ (y ≠ x ∧ env y e i)) (shiftL c x) w y := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun e i hp => Or.inr ⟨hyx, h1 e i hp⟩, ?_, ?_⟩
  · rcases shiftL_ne c x y hyx with ⟨_, h6⟩ | ⟨_, h6⟩ <;> omega
  · intro hw
    rcases shiftL_ne c x y hyx with ⟨_, h6⟩ | ⟨_, h6⟩ <;>
      rcases shiftL_ne c x w hwx with ⟨_, h7⟩ | ⟨_, h7⟩ <;> omega

theorem ks_prom {D' : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (hK : KS D' j f env c Pi) (u v w : ℕ) (_huw : u ≠ w) (hvw : v ≠ w)
    (huv : u ≠ v) (ka kb : Bool) (hua : u ∈ D' ↔ ka = true) (hvb : v ∈ D' ↔ kb = true) :
    ∃ (j2 : ℕ) (env2 : ℕ → ℕ → ℕ → Prop) (c2 : ℕ → ℕ) (Pi2 : ℕ → ℕ → ℕ → Prop),
      KS D' j2 f env2 c2 Pi2 ∧ j2 = j + (cond ka 1 0 + cond kb 1 0) ∧
      (u ∈ D' → Prom env2 c2 w u) ∧ (v ∈ D' → Prom env2 c2 w v) := by
  cases ka <;> cases kb
  · exact ⟨j, env, c, Pi, hK, rfl, fun h => Bool.noConfusion (hua.mp h),
      fun h => Bool.noConfusion (hvb.mp h)⟩
  · exact ⟨_, _, _, _, hK.promote v (hvb.mpr rfl), rfl, fun h => Bool.noConfusion (hua.mp h),
      fun _ => prom_self env c w v⟩
  · exact ⟨_, _, _, _, hK.promote u (hua.mpr rfl), rfl, fun _ => prom_self env c w u,
      fun h => Bool.noConfusion (hvb.mp h)⟩
  · exact ⟨_, _, _, _, (hK.promote u (hua.mpr rfl)).promote v (hvb.mpr rfl), rfl,
      fun _ => prom_other _ _ w v u huv (Ne.symm hvw) (prom_self env c w u),
      fun _ => prom_self _ _ w v⟩

theorem KS.step {D D' : Finset ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS D' j f env c Pi) (u v w : ℕ) (hu : u ∈ D) (hv : v ∈ D)
    (huv : u ≠ v) (hwD : w ∉ D) (hw : w ∈ D') (hD' : ∀ x ∈ D', x ≠ w → x ∈ D)
    (cc : ℕ → ℕ → Bool)
    (hcu : ∀ e i, Pc w e i → cc e i = true → Pc u e i)
    (hcv : ∀ e i, Pc w e i → cc e i = false → Pc v e i)
    (hcr : ∀ (b : Bool) (e i e' i' : ℕ), cc e i = b → cc e' i' = b → cc e i' = b)
    (hku : u ∈ D' → Prom env c w u) (hkv : v ∈ D' → Prom env c w v) :
    ∃ (f2 : ℕ → ℕ → ℕ) (env2 : ℕ → ℕ → ℕ → Prop) (c2 : ℕ → ℕ), KS D j f2 env2 c2 Pi := by
  have hc2a : ∀ x, x ∈ D' → (if x ∈ D' then c x else c w) = c x := fun x hx => ite_p _ _ hx
  have hc2b : ∀ x, x ∉ D' → (if x ∈ D' then c x else c w) = c w := fun x hx => ite_n _ _ hx
  refine ⟨fun e i => if f e i = w then cond (cc e i) u v else f e i,
    fun x e i => (x ∈ D' ∧ env x e i) ∨
      (x ∉ D' ∧ env w e i ∧ ((x = u ∧ cc e i = true) ∨ (x = v ∧ cc e i = false))),
    fun x => if x ∈ D' then c x else c w, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e i he hi
    obtain ⟨h1, h2⟩ := h.own e i he hi
    show (if f e i = w then cond (cc e i) u v else f e i) ∈ D ∧
      (((if f e i = w then cond (cc e i) u v else f e i) ∈ D' ∧
        env (if f e i = w then cond (cc e i) u v else f e i) e i) ∨
      ((if f e i = w then cond (cc e i) u v else f e i) ∉ D' ∧ env w e i ∧
        (((if f e i = w then cond (cc e i) u v else f e i) = u ∧ cc e i = true) ∨
         ((if f e i = w then cond (cc e i) u v else f e i) = v ∧ cc e i = false))))
    by_cases hfw : f e i = w
    · rw [ite_p _ _ hfw]
      rw [hfw] at h2
      have hpw := h.envP w hw e i h2
      cases hcc : cc e i
      · refine ⟨hv, ?_⟩
        by_cases hvD : v ∈ D'
        · exact Or.inl ⟨hvD, (hkv hvD).1 e i (hcv e i hpw hcc)⟩
        · exact Or.inr ⟨hvD, h2, Or.inr ⟨rfl, rfl⟩⟩
      · refine ⟨hu, ?_⟩
        by_cases huD : u ∈ D'
        · exact Or.inl ⟨huD, (hku huD).1 e i (hcu e i hpw hcc)⟩
        · exact Or.inr ⟨huD, h2, Or.inl ⟨rfl, rfl⟩⟩
    · rw [ite_n _ _ hfw]
      exact ⟨hD' _ h1 hfw, Or.inl ⟨h1, h2⟩⟩
  · intro x _ e i e' i' h1 h2
    rcases h1 with ⟨hx, h1⟩ | ⟨hx, h1, h1c⟩ <;> rcases h2 with ⟨hx', h2⟩ | ⟨hx', h2, h2c⟩
    · exact Or.inl ⟨hx, h.envR x hx e i e' i' h1 h2⟩
    · exact absurd hx hx'
    · exact absurd hx' hx
    · refine Or.inr ⟨hx, h.envR w hw e i e' i' h1 h2, ?_⟩
      rcases h1c with ⟨hxu, hc1⟩ | ⟨hxv, hc1⟩ <;> rcases h2c with ⟨hxu', hc2⟩ | ⟨hxv', hc2⟩
      · exact Or.inl ⟨hxu, hcr true e i e' i' hc1 hc2⟩
      · exact absurd (hxu.symm.trans hxv') huv
      · exact absurd (hxu'.symm.trans hxv) huv
      · exact Or.inr ⟨hxv, hcr false e i e' i' hc1 hc2⟩
  · intro x _ e i h1
    rcases h1 with ⟨hx, h1⟩ | ⟨_, h1, h1c⟩
    · exact h.envP x hx e i h1
    · have hpw := h.envP w hw e i h1
      rcases h1c with ⟨hxu, hc1⟩ | ⟨hxv, hc1⟩
      · rw [hxu]; exact hcu e i hpw hc1
      · rw [hxv]; exact hcv e i hpw hc1
  · intro x hx y hy hxy hc e i h1 h2
    have hxw : x ≠ w := fun hh => hwD (hh ▸ hx)
    have hyw : y ≠ w := fun hh => hwD (hh ▸ hy)
    have hc' : (if x ∈ D' then c x else c w) = (if y ∈ D' then c y else c w) := hc
    rcases h1 with ⟨hx', h1⟩ | ⟨hx', h1, h1c⟩ <;> rcases h2 with ⟨hy', h2⟩ | ⟨hy', h2, h2c⟩
    · rw [hc2a x hx', hc2a y hy'] at hc'
      exact h.s1 x hx' y hy' hxy hc' e i h1 h2
    · rw [hc2a x hx', hc2b y hy'] at hc'
      exact h.s1 x hx' w hw hxw hc' e i h1 h2
    · rw [hc2b x hx', hc2a y hy'] at hc'
      exact h.s1 w hw y hy' (Ne.symm hyw) hc' e i h1 h2
    · rcases h1c with ⟨hxu, hc1⟩ | ⟨hxv, hc1⟩ <;> rcases h2c with ⟨hyu, hc2⟩ | ⟨hyv, hc2⟩
      · exact hxy (hxu.trans hyu.symm)
      · rw [hc1] at hc2; exact Bool.noConfusion hc2
      · rw [hc1] at hc2; exact Bool.noConfusion hc2
      · exact hxy (hxv.trans hyv.symm)
  · intro x _ hc e i h1
    have hc' : 1 ≤ (if x ∈ D' then c x else c w) := hc
    show Pi (if x ∈ D' then c x else c w) e i
    rcases h1 with ⟨hx', h1⟩ | ⟨hx', h1, _⟩
    · rw [hc2a x hx'] at hc' ⊢
      exact h.s2 x hx' hc' e i h1
    · rw [hc2b x hx'] at hc' ⊢
      exact h.s2 w hw hc' e i h1
  · exact h.piR
  · intro n e i hn h1
    obtain ⟨y, hy, h3, h4, h5⟩ := h.s3 n e i hn h1
    show ∃ y ∈ D, 1 ≤ (if y ∈ D' then c y else c w) ∧ (if y ∈ D' then c y else c w) ≤ n ∧ Pc y e i
    by_cases hyw : y = w
    · rw [hyw] at h3 h4 h5
      cases hcc : cc e i
      · refine ⟨v, hv, ?_, ?_, hcv e i h5 hcc⟩
        · by_cases hvD : v ∈ D'
          · rw [hc2a v hvD]; exact (hkv hvD).2.1
          · rw [hc2b v hvD]; exact h3
        · by_cases hvD : v ∈ D'
          · rw [hc2a v hvD]; exact le_trans ((hkv hvD).2.2 h3) h4
          · rw [hc2b v hvD]; exact h4
      · refine ⟨u, hu, ?_, ?_, hcu e i h5 hcc⟩
        · by_cases huD : u ∈ D'
          · rw [hc2a u huD]; exact (hku huD).2.1
          · rw [hc2b u huD]; exact h3
        · by_cases huD : u ∈ D'
          · rw [hc2a u huD]; exact le_trans ((hku huD).2.2 h3) h4
          · rw [hc2b u huD]; exact h4
    · exact ⟨y, hD' y hy hyw, by rw [hc2a y hy]; exact h3, by rw [hc2a y hy]; exact h4, h5⟩
  · intro x _
    show (if x ∈ D' then c x else c w) ≤ j
    by_cases hx' : x ∈ D'
    · rw [hc2a x hx']; exact h.lab x hx'
    · rw [hc2b x hx']; exact h.lab w hw

theorem cond_sum (b : Bool) : (cond b 1 0 : ℕ) + cond b 0 1 = 1 := by cases b <;> rfl

theorem Reach.ks {m : Bool} {D : Finset ℕ} {k : ℕ} (h : Reach m D k) :
    ∃ (j : ℕ) (f : ℕ → ℕ → ℕ) (env : ℕ → ℕ → ℕ → Prop) (c : ℕ → ℕ) (Pi : ℕ → ℕ → ℕ → Prop),
      KS D j f env c Pi ∧ j + D.card ≤ k + 1 := by
  induction h using Reach.ind with
  | done k => exact ⟨0, _, _, _, _, ks_done, by simp⟩
  | step D k u v w ka kb hu hv hw hd hb hR ih =>
    obtain ⟨j, f, env, c, Pi, hK, hj⟩ := ih
    have hwD : w ∉ D := fun hm => by
      have := hd w hm
      rw [blk_refl] at this
      exact Bool.noConfusion this
    have hwu : w ≠ u := fun h => hwD (h ▸ hu)
    have hwv : w ≠ v := fun h => hwD (h ▸ hv)
    have huv : u ≠ v := by
      rintro rfl
      rcases hw with hw | hw
      · rw [Nat.and_self] at hw; exact hwu hw
      · rw [Nat.or_self] at hw; exact hwu hw
    have hwF : w ∉ D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v)) :=
      fun hm => hwD (Finset.mem_of_mem_filter _ hm)
    rw [Finset.card_insert_of_notMem hwF] at hj
    have hsz := size_lb2 D u v ka kb
    generalize (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))).card = size at hj hsz
    have hua : u ∈ insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) ↔
        ka = true := by
      rw [Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro (h | ⟨_, h, _⟩)
        · exact absurd h.symm hwu
        · exact h.resolve_right (fun hh => hh rfl)
      · intro h
        exact Or.inr ⟨hu, Or.inl h, Or.inr huv⟩
    have hvb : v ∈ insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))) ↔
        kb = true := by
      rw [Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro (h | ⟨_, _, h⟩)
        · exact absurd h.symm hwv
        · exact h.resolve_right (fun hh => hh rfl)
      · intro h
        exact Or.inr ⟨hv, Or.inr (Ne.symm huv), Or.inl h⟩
    obtain ⟨j2, env2, c2, Pi2, hK2, hj2, hpu, hpv⟩ :=
      ks_prom hK u v w (Ne.symm hwu) (Ne.symm hwv) huv ka kb hua hvb
    have hD' : ∀ x ∈ insert w (D.filter (fun x => (ka = true ∨ x ≠ u) ∧ (kb = true ∨ x ≠ v))),
        x ≠ w → x ∈ D := by
      intro x hx hxw
      rcases Finset.mem_insert.mp hx with h | h
      · exact absurd h hxw
      · exact Finset.mem_of_mem_filter _ h
    have hfin : ∃ (f2 : ℕ → ℕ → ℕ) (env3 : ℕ → ℕ → ℕ → Prop) (c3 : ℕ → ℕ),
        KS D j2 f2 env3 c3 Pi2 := by
      rcases hw with rfl | rfl
      · exact hK2.step u v (u &&& v) hu hv huv hwD (Finset.mem_insert_self _ _) hD'
          (fun _ i => !(u.testBit i))
          (fun e i h1 h3 => and_cu u v e i h1.1 h1.2 h3)
          (fun e i h1 h3 => and_cv u v e i h1.1 h1.2 h3)
          (fun b e i e' i' _ h2 => h2) hpu hpv
      · exact hK2.step u v (u ||| v) hu hv huv hwD (Finset.mem_insert_self _ _) hD'
          (fun e _ => u.testBit e)
          (fun e i h1 h3 => or_cu u v e i h1.1 h1.2 h3)
          (fun e i h1 h3 => or_cv u v e i h1.1 h1.2 h3)
          (fun b e i e' i' h1 _ => h1) hpu hpv
    obtain ⟨f2, env3, c3, hK3⟩ := hfin
    refine ⟨j2, f2, env3, c3, Pi2, hK3, ?_⟩
    have e1 := cond_sum ka
    have e2 := cond_sum kb
    omega

def MS (l : List ℕ) (j : ℕ) (Env : ℕ → ℕ → Prop) (c : ℕ → ℕ) (PiM : ℕ → ℕ → Prop) : Prop :=
  (∀ q, q < 144 → ∃ x ∈ l, Env x q) ∧
  (∀ x ∈ l, IsRect (Env x)) ∧
  (∀ x ∈ l, ∀ q, Env x q → q < 144 ∧ (rectW x).testBit q = true) ∧
  (∀ x ∈ l, ∀ y ∈ l, x ≠ y → c x = c y → ∀ q, Env x q → Env y q → False) ∧
  (∀ x ∈ l, 1 ≤ c x → ∀ q, Env x q → PiM (c x) q) ∧
  (∀ n, IsRect (PiM n)) ∧
  (∀ n q, 1 ≤ n → PiM n q → ∃ y ∈ l, 1 ≤ c y ∧ c y ≤ n ∧ (rectW y).testBit q = true) ∧
  (∀ x ∈ l, c x ≤ j)

theorem MS.own {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ q, q < 144 → ∃ x ∈ l, Env x q := h.1

theorem MS.envR {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ x ∈ l, IsRect (Env x) := h.2.1

theorem MS.envB {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ x ∈ l, ∀ q, Env x q → q < 144 ∧ (rectW x).testBit q = true := h.2.2.1

theorem MS.s1 {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ x ∈ l, ∀ y ∈ l, x ≠ y → c x = c y → ∀ q, Env x q → Env y q → False := h.2.2.2.1

theorem MS.s2 {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ x ∈ l, 1 ≤ c x → ∀ q, Env x q → PiM (c x) q := h.2.2.2.2.1

theorem MS.piR {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ n, IsRect (PiM n) := h.2.2.2.2.2.1

theorem MS.s3 {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ n q, 1 ≤ n → PiM n q → ∃ y ∈ l, 1 ≤ c y ∧ c y ≤ n ∧ (rectW y).testBit q = true := h.2.2.2.2.2.2.1

theorem MS.lab {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop} (h : MS l j Env c PiM) :
    ∀ x ∈ l, c x ≤ j := h.2.2.2.2.2.2.2


theorem rect_conv (S : ℕ → ℕ → Prop) (hS : IsRect2 S) :
    IsRect (fun q => q < 144 ∧ S (q / 12) (12 + q % 12)) := by
  intro e i e' i' he hi he' hi' h1 h2
  have h1' : S ((12 * e + i) / 12) (12 + (12 * e + i) % 12) := h1.2
  have h2' : S ((12 * e' + i') / 12) (12 + (12 * e' + i') % 12) := h2.2
  have e1 : (12 * e + i) / 12 = e := by omega
  have e2 : (12 * e + i) % 12 = i := by omega
  have e3 : (12 * e' + i') / 12 = e' := by omega
  have e4 : (12 * e' + i') % 12 = i' := by omega
  have e5 : (12 * e + i') / 12 = e := by omega
  have e6 : (12 * e + i') % 12 = i' := by omega
  rw [e1, e2] at h1'
  rw [e3, e4] at h2'
  show 12 * e + i' < 144 ∧ S ((12 * e + i') / 12) (12 + (12 * e + i') % 12)
  rw [e5, e6]
  exact ⟨by omega, hS _ _ _ _ h1' h2'⟩

theorem pc_bit (x q : ℕ) (hq : q < 144) (h : Pc x (q / 12) (12 + q % 12)) :
    (rectW x).testBit q = true := by
  have h3 := rectW_tb x (q / 12) (q % 12) (by omega) (Nat.mod_lt _ (by norm_num)) h.1 h.2
  rwa [Nat.div_add_mod] at h3

theorem KS.toMS {l : List ℕ} {j : ℕ} {f : ℕ → ℕ → ℕ} {env : ℕ → ℕ → ℕ → Prop} {c : ℕ → ℕ}
    {Pi : ℕ → ℕ → ℕ → Prop} (h : KS l.toFinset j f env c Pi) :
    MS l j (fun x q => q < 144 ∧ env x (q / 12) (12 + q % 12)) c
      (fun n q => q < 144 ∧ Pi n (q / 12) (12 + q % 12)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨h1, h2⟩ := h.own (q / 12) (12 + q % 12) (by omega) (by omega)
    exact ⟨_, List.mem_toFinset.mp h1, hq, h2⟩
  · intro x hx
    exact rect_conv _ (h.envR x (List.mem_toFinset.mpr hx))
  · intro x hx q hq
    exact ⟨hq.1, pc_bit x q hq.1 (h.envP x (List.mem_toFinset.mpr hx) _ _ hq.2)⟩
  · intro x hx y hy hxy hc q h1 h2
    exact h.s1 x (List.mem_toFinset.mpr hx) y (List.mem_toFinset.mpr hy) hxy hc _ _ h1.2 h2.2
  · intro x hx hc q h1
    exact ⟨h1.1, h.s2 x (List.mem_toFinset.mpr hx) hc _ _ h1.2⟩
  · intro n
    exact rect_conv _ (h.piR n)
  · intro n q hn h1
    obtain ⟨y, hy, h3, h4, h5⟩ := h.s3 n _ _ hn h1.2
    exact ⟨y, List.mem_toFinset.mp hy, h3, h4, pc_bit y q h1.1 h5⟩
  · intro x hx
    exact h.lab x (List.mem_toFinset.mpr hx)

theorem MS.priv_env {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop}
    (hM : MS l j Env c PiM) : ∀ y ∈ l, ∀ q,
    (priv (tw (l.map rectW) 0 0) (rectW y)).testBit q = true → Env y q := by
  intro y hy q hq
  obtain ⟨hq144, i, e', hi, he', ha, hb⟩ := hull_spec _ q hq
  have key : ∀ x, x < 144 →
      (Nat.land (rectW y) (Nat.xor (tw (l.map rectW) 0 0) full)).testBit x = true → Env y x := by
    intro x hx hbit
    rw [tb_land, tb_xor, full_tb, Bool.and_eq_true] at hbit
    obtain ⟨hzx, ht⟩ := hbit
    have ht' : (tw (l.map rectW) 0 0).testBit x = false := by simpa [hx] using ht
    obtain ⟨_, _, hpw⟩ := tw_spec x _ 0 0 ht'
    rw [List.pairwise_map] at hpw
    obtain ⟨z, hz, hzq⟩ := hM.own x hx
    by_cases hzz : z = y
    · rw [← hzz]; exact hzq
    · exfalso
      exact pw_forall (fun a b h h' => h ⟨h'.2, h'.1⟩) l hpw z hz y hy hzz
        ⟨(hM.envB z hz x hzq).2, hzx⟩
  have h1 := key _ (by omega) ha
  have h2 := key _ (by omega) hb
  have h3 := hM.envR y hy (q / 12) i e' (q % 12) (by omega) hi he' (Nat.mod_lt _ (by norm_num))
    h1 h2
  rwa [Nat.div_add_mod] at h3

def ValidLab (l : List ℕ) (K : ℕ) (c : ℕ → ℕ) : Prop :=
  (∀ x ∈ l, c x ≤ K) ∧
  (∀ x ∈ l, ∀ y ∈ l, x ≠ y → c x = c y →
    Nat.land (priv (tw (l.map rectW) 0 0) (rectW x)) (priv (tw (l.map rectW) 0 0) (rectW y)) = 0) ∧
  (∀ i U : ℕ, 1 ≤ i →
    (∀ q, U.testBit q = true →
      ∃ x ∈ l, c x = i ∧ (priv (tw (l.map rectW) 0 0) (rectW x)).testBit q = true) →
    ∀ q, (hull U).testBit q = true → ∃ y ∈ l, 1 ≤ c y ∧ c y ≤ i ∧ (rectW y).testBit q = true) ∧
  (∀ x ∈ l, ∀ q, (priv (tw (l.map rectW) 0 0) (rectW x)).testBit q = true →
    (rectW x).testBit q = true)

theorem MS.validLab {l : List ℕ} {j : ℕ} {Env : ℕ → ℕ → Prop} {c : ℕ → ℕ} {PiM : ℕ → ℕ → Prop}
    (hM : MS l j Env c PiM) (K : ℕ) (hK : j ≤ K) : ValidLab l K c := by
  refine ⟨fun x hx => le_trans (hM.lab x hx) hK, ?_, ?_, ?_⟩
  · intro x hx y hy hxy hc
    exact land_disj _ _ (fun q h1 h2 =>
      hM.s1 x hx y hy hxy hc q (hM.priv_env x hx q h1) (hM.priv_env y hy q h2))
  · intro i U hi hU q hq
    obtain ⟨_, a, e', ha, he', h1, h2⟩ := hull_spec _ q hq
    obtain ⟨x1, hx1, hc1, hb1⟩ := hU _ h1
    obtain ⟨x2, hx2, hc2, hb2⟩ := hU _ h2
    have hp1 := hM.s2 x1 hx1 (by omega) _ (hM.priv_env x1 hx1 _ hb1)
    have hp2 := hM.s2 x2 hx2 (by omega) _ (hM.priv_env x2 hx2 _ hb2)
    rw [hc1] at hp1
    rw [hc2] at hp2
    have h3 := hM.piR i (q / 12) a e' (q % 12) (by omega) ha he' (Nat.mod_lt _ (by norm_num))
      hp1 hp2
    rw [Nat.div_add_mod] at h3
    exact hM.s3 i q hi h3
  · intro x hx q hq
    exact (hM.envB x hx q (hM.priv_env x hx q hq)).2

theorem reach_validLab {m : Bool} {l : List ℕ} {k : ℕ} (hnd : l.Nodup) (hR : Reach m l.toFinset k) :
    ∃ c : ℕ → ℕ, ValidLab l (Nat.sub (Nat.succ k) l.length) c := by
  obtain ⟨j, f, env, c, Pi, hK, hj⟩ := hR.ks
  rw [List.toFinset_card_of_nodup hnd] at hj
  exact ⟨c, hK.toMS.validLab _ (by
    show j ≤ (k + 1) - l.length
    omega)⟩

def fld (x i : ℕ) : ℕ := Nat.land (Nat.shiftRight x (Nat.mul 144 i)) full

def put (x i v : ℕ) : ℕ := Nat.lor x (Nat.shiftLeft v (Nat.mul 144 i))

def subM (h c : ℕ) : Bool := Nat.beq (Nat.land h c) h

def chkA (bc hs cs K : ℕ) : ℕ → ℕ → Bool
  | 0, _ => true
  | n + 1, pre =>
    subM (fld hs (Nat.sub K n)) (Nat.lor bc (Nat.lor pre (fld cs (Nat.sub K n)))) &&
    chkA bc hs cs K n (Nat.lor pre (fld cs (Nat.sub K n)))

def tryL (K bc a h : ℕ) (cont : ℕ → ℕ → ℕ → Bool) (us hs cs : ℕ) : ℕ → Bool
  | 0 => false
  | n + 1 =>
    (Nat.beq (Nat.land (fld us (Nat.sub K n)) h) 0 &&
      (chkA bc (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
          (put cs (Nat.sub K n) a) K K 0 &&
        cont (put us (Nat.sub K n) h)
          (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
          (put cs (Nat.sub K n) a))) ||
    tryL K bc a h cont us hs cs n

def orA : List ℕ → ℕ
  | [] => 0
  | it :: r => Nat.lor (fld it 0) (orA r)

def go (K base : ℕ) : List ℕ → ℕ → ℕ → ℕ → Bool
  | [] => fun _ _ _ => true
  | it :: rest => fun us hs cs =>
    tryL K (Nat.lor base (orA rest)) (fld it 0) (fld it 1) (go K base rest) us hs cs (Nat.succ K)

def vs (t t2 : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: l => cond (Nat.beq (Nat.land (priv t a) t2) 0) (vs t t2 l)
      (put (Nat.land a full) 1 (priv t a) :: vs t t2 l)

def fcov (t t2 : ℕ) : List ℕ → ℕ
  | [] => 0
  | a :: l => cond (Nat.beq (Nat.land (priv t a) t2) 0) (Nat.lor a (fcov t t2 l)) (fcov t t2 l)

def degI (x : ℕ) : List ℕ → ℕ
  | [] => 0
  | y :: l => cond (Nat.beq (Nat.land (fld y 1) (fld x 1)) 0) (degI x l) (Nat.succ (degI x l))

def insD (all : List ℕ) (x : ℕ) : List ℕ → List ℕ
  | [] => [x]
  | y :: l => cond (Nat.blt (degI y all) (degI x all)) (x :: y :: l) (y :: insD all x l)

def sortD (all : List ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: l => insD all x (sortD all l)

theorem insD_perm (all : List ℕ) (x : ℕ) : ∀ l : List ℕ, (insD all x l).Perm (x :: l) := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons y l ih =>
    unfold insD
    cases Nat.blt (degI y all) (degI x all)
    · exact (List.Perm.cons y ih).trans (List.Perm.swap x y l)
    · exact List.Perm.refl _

theorem sortD_perm (all : List ℕ) : ∀ l : List ℕ, (sortD all l).Perm l := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons x l ih => exact (insD_perm all x _).trans (List.Perm.cons x ih)

def classP3 (K t t2 : ℕ) (as : List ℕ) : Bool :=
  go K (fcov t t2 as)
    (cond (Nat.blt 1 K) (sortD (vs t t2 as) (vs t t2 as)) (vs t t2 as)) 0 0 0

def classP2 (K : ℕ) (as : List ℕ) (t : ℕ) : Bool := classP3 K t (tw (as.map (priv t)) 0 0) as

def classP (l : List ℕ) (k : ℕ) : Bool :=
  classP2 (Nat.sub (Nat.succ k) l.length) (l.map rectW) (tw (l.map rectW) 0 0)
def chkA' (bc hs cs K n : ℕ) : ℕ → Bool :=
  @Nat.rec (fun _ => ℕ → Bool) (fun _ => true)
    (fun n ih pre => band (subM (fld hs (Nat.sub K n)) (Nat.lor bc (Nat.lor pre (fld cs (Nat.sub K n)))))
      (ih (Nat.lor pre (fld cs (Nat.sub K n))))) n

theorem chkA'_eq (bc hs cs K n : ℕ) : ∀ pre : ℕ, chkA' bc hs cs K n pre = chkA bc hs cs K n pre := by
  induction n with
  | zero => intro pre; rfl
  | succ n ih =>
    intro pre
    show band (subM (fld hs (Nat.sub K n)) (Nat.lor bc (Nat.lor pre (fld cs (Nat.sub K n)))))
      (chkA' bc hs cs K n (Nat.lor pre (fld cs (Nat.sub K n)))) =
      (subM (fld hs (Nat.sub K n)) (Nat.lor bc (Nat.lor pre (fld cs (Nat.sub K n)))) &&
        chkA bc hs cs K n (Nat.lor pre (fld cs (Nat.sub K n))))
    rw [ih, band_eq]

def tryL' (K bc a h : ℕ) (cont : ℕ → ℕ → ℕ → Bool) (us hs cs n : ℕ) : Bool :=
  @Nat.rec (fun _ => Bool) false
    (fun n ih => bor
      (band (Nat.beq (Nat.land (fld us (Nat.sub K n)) h) 0)
        (band (chkA' bc (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
            (put cs (Nat.sub K n) a) K K 0)
          (cont (put us (Nat.sub K n) h)
            (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
            (put cs (Nat.sub K n) a))))
      ih) n

theorem tryL'_eq (K bc a h : ℕ) (cont : ℕ → ℕ → ℕ → Bool) (us hs cs n : ℕ) :
    tryL' K bc a h cont us hs cs n = tryL K bc a h cont us hs cs n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show bor
      (band (Nat.beq (Nat.land (fld us (Nat.sub K n)) h) 0)
        (band (chkA' bc (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
            (put cs (Nat.sub K n) a) K K 0)
          (cont (put us (Nat.sub K n) h)
            (put hs (Nat.sub K n) (hull (Nat.lor (fld us (Nat.sub K n)) h)))
            (put cs (Nat.sub K n) a))))
      (tryL' K bc a h cont us hs cs n) = tryL K bc a h cont us hs cs (n + 1)
    rw [ih, bor_eq, band_eq, band_eq, chkA'_eq]
    rfl

def orA' (l : List ℕ) : ℕ := @List.rec ℕ (fun _ => ℕ) 0 (fun it _ ih => Nat.lor (fld it 0) ih) l

theorem orA'_eq (l : List ℕ) : orA' l = orA l := by
  induction l with
  | nil => rfl
  | cons it r ih => show Nat.lor (fld it 0) (orA' r) = Nat.lor (fld it 0) (orA r); rw [ih]

def go' (K base : ℕ) (l : List ℕ) : ℕ → ℕ → ℕ → Bool :=
  @List.rec ℕ (fun _ => ℕ → ℕ → ℕ → Bool) (fun _ _ _ => true)
    (fun it rest ih us hs cs =>
      tryL' K (Nat.lor base (orA' rest)) (fld it 0) (fld it 1) ih us hs cs (Nat.succ K)) l

theorem go'_eq (K base : ℕ) (l : List ℕ) : go' K base l = go K base l := by
  induction l with
  | nil => rfl
  | cons it rest ih =>
    funext us hs cs
    show tryL' K (Nat.lor base (orA' rest)) (fld it 0) (fld it 1) (go' K base rest) us hs cs
      (Nat.succ K) = tryL K (Nat.lor base (orA rest)) (fld it 0) (fld it 1) (go K base rest) us hs cs
      (Nat.succ K)
    rw [ih, orA'_eq, tryL'_eq]

def vs' (t t2 : ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) []
    (fun a _ ih => @Bool.rec (fun _ => List ℕ) (put (Nat.land a full) 1 (priv t a) :: ih) ih
      (Nat.beq (Nat.land (priv t a) t2) 0)) l

theorem vs'_eq (t t2 : ℕ) (l : List ℕ) : vs' t t2 l = vs t t2 l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show @Bool.rec (fun _ => List ℕ) (put (Nat.land a full) 1 (priv t a) :: vs' t t2 l) (vs' t t2 l)
      (Nat.beq (Nat.land (priv t a) t2) 0) =
      cond (Nat.beq (Nat.land (priv t a) t2) 0) (vs t t2 l)
        (put (Nat.land a full) 1 (priv t a) :: vs t t2 l)
    rw [ih]
    cases Nat.beq (Nat.land (priv t a) t2) 0 <;> rfl

def fcov' (t t2 : ℕ) (l : List ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ) 0
    (fun a _ ih => @Bool.rec (fun _ => ℕ) ih (Nat.lor a ih) (Nat.beq (Nat.land (priv t a) t2) 0)) l

theorem fcov'_eq (t t2 : ℕ) (l : List ℕ) : fcov' t t2 l = fcov t t2 l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    show @Bool.rec (fun _ => ℕ) (fcov' t t2 l) (Nat.lor a (fcov' t t2 l))
      (Nat.beq (Nat.land (priv t a) t2) 0) =
      cond (Nat.beq (Nat.land (priv t a) t2) 0) (Nat.lor a (fcov t t2 l)) (fcov t t2 l)
    rw [ih]
    cases Nat.beq (Nat.land (priv t a) t2) 0 <;> rfl

def degI' (x : ℕ) (l : List ℕ) : ℕ :=
  @List.rec ℕ (fun _ => ℕ) 0
    (fun y _ ih => @Bool.rec (fun _ => ℕ) (Nat.succ ih) ih
      (Nat.beq (Nat.land (fld y 1) (fld x 1)) 0)) l

theorem degI'_eq (x : ℕ) (l : List ℕ) : degI' x l = degI x l := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    show @Bool.rec (fun _ => ℕ) (Nat.succ (degI' x l)) (degI' x l)
      (Nat.beq (Nat.land (fld y 1) (fld x 1)) 0) =
      cond (Nat.beq (Nat.land (fld y 1) (fld x 1)) 0) (degI x l) (Nat.succ (degI x l))
    rw [ih]
    cases Nat.beq (Nat.land (fld y 1) (fld x 1)) 0 <;> rfl

def insD' (all : List ℕ) (x : ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [x]
    (fun y t ih => @Bool.rec (fun _ => List ℕ) (y :: ih) (x :: y :: t)
      (Nat.blt (degI' y all) (degI' x all))) l

theorem insD'_eq (all : List ℕ) (x : ℕ) (l : List ℕ) : insD' all x l = insD all x l := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    show @Bool.rec (fun _ => List ℕ) (y :: insD' all x l) (x :: y :: l)
      (Nat.blt (degI' y all) (degI' x all)) =
      cond (Nat.blt (degI y all) (degI x all)) (x :: y :: l) (y :: insD all x l)
    rw [ih, degI'_eq, degI'_eq]
    cases Nat.blt (degI y all) (degI x all) <;> rfl

def sortD' (all : List ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [] (fun x _ ih => insD' all x ih) l

theorem sortD'_eq (all : List ℕ) (l : List ℕ) : sortD' all l = sortD all l := by
  induction l with
  | nil => rfl
  | cons x l ih => show insD' all x (sortD' all l) = insD all x (sortD all l); rw [ih, insD'_eq]

def mapP' (t : ℕ) (l : List ℕ) : List ℕ :=
  @List.rec ℕ (fun _ => List ℕ) [] (fun a _ ih => priv t a :: ih) l

theorem mapP'_eq (t : ℕ) (l : List ℕ) : mapP' t l = l.map (priv t) := by
  induction l with
  | nil => rfl
  | cons a l ih => show priv t a :: mapP' t l = priv t a :: l.map (priv t); rw [ih]

def classQ (K : ℕ) (as : List ℕ) : Bool :=
  (fun t => (fun t2 => (fun items =>
      go' K (fcov' t t2 as)
        (@Bool.rec (fun _ => List ℕ) items (sortD' items items) (Nat.blt 1 K)) 0 0 0)
    (vs' t t2 as)) (tw' (mapP' t as) 0 0)) (tw' as 0 0)

def classP' (l : List ℕ) (k : ℕ) : Bool := classQ (Nat.sub (Nat.succ k) (l.length)) (mapW' l)

theorem classP'_eq (l : List ℕ) (k : ℕ) : classP' l k = classP l k := by
  show go' _ (fcov' _ _ (mapW' l))
    (@Bool.rec (fun _ => List ℕ) (vs' _ _ (mapW' l)) (sortD' (vs' _ _ (mapW' l)) (vs' _ _ (mapW' l)))
      (Nat.blt 1 (Nat.sub (Nat.succ k) (l.length)))) 0 0 0 = classP l k
  rw [mapW'_eq, tw'_eq, mapP'_eq, tw'_eq, go'_eq, fcov'_eq, vs'_eq, sortD'_eq]
  unfold classP classP2 classP3
  cases Nat.blt 1 (Nat.sub (Nat.succ k) l.length) <;> rfl

def privH (l : List ℕ) (x : ℕ) : ℕ := priv (tw (l.map rectW) 0 0) (rectW x)

def t2Of (l : List ℕ) : ℕ := tw ((l.map rectW).map (priv (tw (l.map rectW) 0 0))) 0 0

def isConf (l : List ℕ) (x : ℕ) : Prop := Nat.land (privH l x) (t2Of l) ≠ 0

def ClassLab (l : List ℕ) (K : ℕ) (c : ℕ → ℕ) : Prop :=
  (∀ x ∈ l, isConf l x → c x ≤ K) ∧
  (l.Pairwise (fun x y => isConf l x → isConf l y → c x = c y →
        Nat.land (privH l x) (privH l y) = 0)) ∧
  (∀ i U : ℕ, 1 ≤ i → i ≤ K →
        (∀ r, U.testBit r = true →
          ∃ x ∈ l, isConf l x ∧ c x = i ∧ (privH l x).testBit r = true) →
        ∀ q, (hull U).testBit q = true →
        ∃ y ∈ l, (rectW y).testBit q = true ∧ (isConf l y → 1 ≤ c y ∧ c y ≤ i))

theorem ClassLab.le {l : List ℕ} {K : ℕ} {c : ℕ → ℕ} (h : ClassLab l K c) :
    ∀ x ∈ l, isConf l x → c x ≤ K := h.1

theorem ClassLab.ne {l : List ℕ} {K : ℕ} {c : ℕ → ℕ} (h : ClassLab l K c) :
    l.Pairwise (fun x y => isConf l x → isConf l y → c x = c y →
        Nat.land (privH l x) (privH l y) = 0) := h.2.1

theorem ClassLab.cov {l : List ℕ} {K : ℕ} {c : ℕ → ℕ} (h : ClassLab l K c) :
    ∀ i U : ℕ, 1 ≤ i → i ≤ K →
        (∀ r, U.testBit r = true →
          ∃ x ∈ l, isConf l x ∧ c x = i ∧ (privH l x).testBit r = true) →
        ∀ q, (hull U).testBit q = true →
        ∃ y ∈ l, (rectW y).testBit q = true ∧ (isConf l y → 1 ≤ c y ∧ c y ≤ i) := h.2.2


theorem ValidLab.classLab {l : List ℕ} {K : ℕ} {c : ℕ → ℕ} (hnd : l.Nodup)
    (h : ValidLab l K c) : ClassLab l K c := by
  obtain ⟨h1, h2, h3, _⟩ := h
  refine ⟨fun x hx _ => h1 x hx, ?_, ?_⟩
  · have hnd' : l.Pairwise (fun x y => x ≠ y) := hnd
    exact List.Pairwise.imp_of_mem (fun hx hy hxy _ _ hc => h2 _ hx _ hy hxy hc) hnd'
  · intro i U hi1 _ hU q hq
    obtain ⟨y, hy, hc1, hc2, hb⟩ :=
      h3 i U hi1 (fun r hr => (hU r hr).imp (fun x hx => ⟨hx.1, hx.2.2⟩)) q hq
    exact ⟨y, hy, hb, fun _ => ⟨hc1, hc2⟩⟩

theorem fld_tb (x i q : ℕ) :
    (fld x i).testBit q = (x.testBit (144 * i + q) && decide (q < 144)) := by
  unfold fld
  rw [tb_land, full_tb]
  show ((x >>> (144 * i)).testBit q && decide (q < 144)) = _
  rw [Nat.testBit_shiftRight]

theorem put_tb (x i v r : ℕ) :
    (put x i v).testBit r = (x.testBit r || (decide (144 * i ≤ r) && v.testBit (r - 144 * i))) := by
  unfold put
  rw [tb_lor]
  show (x.testBit r || (v <<< (144 * i)).testBit r) = _
  rw [Nat.testBit_shiftLeft]

theorem fld_lt (x i q : ℕ) (h : (fld x i).testBit q = true) : q < 144 := by
  rw [fld_tb, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem fld_zero (j q : ℕ) : (fld 0 j).testBit q = false := by
  rw [fld_tb, Nat.zero_testBit]
  rfl

theorem fld_put_same (x i v q : ℕ) (hv : ∀ r, v.testBit r = true → r < 144) :
    (fld (put x i v) i).testBit q = ((fld x i).testBit q || v.testBit q) := by
  rw [fld_tb, put_tb, fld_tb]
  have e : 144 * i + q - 144 * i = q := by omega
  have e2 : decide (144 * i ≤ 144 * i + q) = true := decide_eq_true (by omega)
  rw [e, e2]
  cases h : v.testBit q
  · simp
  · have e3 : decide (q < 144) = true := decide_eq_true (hv q h)
    rw [e3]
    simp

theorem fld_put_ne (x i j v q : ℕ) (hv : ∀ r, v.testBit r = true → r < 144) (hij : j ≠ i) :
    (fld (put x i v) j).testBit q = (fld x j).testBit q := by
  rw [fld_tb, put_tb, fld_tb]
  by_cases hq : q < 144
  · have e : (decide (144 * i ≤ 144 * j + q) && v.testBit (144 * j + q - 144 * i)) = false := by
      by_cases hle : 144 * i ≤ 144 * j + q
      · have hb : v.testBit (144 * j + q - 144 * i) = false := by
          cases hc : v.testBit (144 * j + q - 144 * i)
          · rfl
          · have := hv _ hc
            omega
        rw [hb]
        exact Bool.and_false _
      · rw [decide_eq_false hle]
        rfl
    rw [e, Bool.or_false]
  · rw [decide_eq_false hq, Bool.and_false, Bool.and_false]

theorem land_zero_tb (a b q : ℕ) (h : Nat.land a b = 0) (ha : a.testBit q = true)
    (hb : b.testBit q = true) : False := by
  have e := tb_land a b q
  rw [h, ha, hb, Nat.zero_testBit] at e
  exact Bool.noConfusion e

theorem chkA_true (bc hs cs K : ℕ)
    (G : ∀ i, 1 ≤ i → i ≤ K → ∀ q, (fld hs i).testBit q = true →
      bc.testBit q = true ∨ ∃ j, 1 ≤ j ∧ j ≤ i ∧ (fld cs j).testBit q = true) :
    ∀ n pre : ℕ, n ≤ K →
      (∀ j, 1 ≤ j → j + n ≤ K → ∀ q, (fld cs j).testBit q = true → pre.testBit q = true) →
      chkA bc hs cs K n pre = true := by
  intro n
  induction n with
  | zero => intro pre _ _; rfl
  | succ n ih =>
    intro pre hn hpre
    show (subM (fld hs (K - n)) (Nat.lor bc (Nat.lor pre (fld cs (K - n)))) &&
      chkA bc hs cs K n (Nat.lor pre (fld cs (K - n)))) = true
    rw [Bool.and_eq_true]
    constructor
    · have e : Nat.land (fld hs (K - n)) (Nat.lor bc (Nat.lor pre (fld cs (K - n)))) =
          fld hs (K - n) := by
        apply land_sub
        intro q hq
        rw [tb_lor, tb_lor]
        rcases G (K - n) (by omega) (by omega) q hq with h | ⟨j, hj1, hj2, hj⟩
        · rw [h]; rfl
        · by_cases hj' : j = K - n
          · subst hj'; rw [hj]; simp
          · rw [hpre j hj1 (by omega) q hj]; simp
      unfold subM
      rw [e]
      exact Nat.beq_refl _
    · apply ih _ (by omega)
      intro j hj1 hj2 q hq
      rw [tb_lor]
      by_cases hj' : j = K - n
      · subst hj'; rw [hq]; simp
      · rw [hpre j hj1 (by omega) q hq]; simp

theorem tryL_true (K bc a h : ℕ) (cont : ℕ → ℕ → ℕ → Bool) (us hs cs j : ℕ)
    (h1 : Nat.land (fld us j) h = 0)
    (h2 : chkA bc (put hs j (hull (Nat.lor (fld us j) h))) (put cs j a) K K 0 = true)
    (h3 : cont (put us j h) (put hs j (hull (Nat.lor (fld us j) h))) (put cs j a) = true) :
    ∀ n : ℕ, j ≤ K → K - j < n → tryL K bc a h cont us hs cs n = true := by
  intro n
  induction n with
  | zero => intro _ hn; omega
  | succ n ih =>
    intro hj hn
    show ((Nat.beq (Nat.land (fld us (K - n)) h) 0 &&
      (chkA bc (put hs (K - n) (hull (Nat.lor (fld us (K - n)) h)))
          (put cs (K - n) a) K K 0 &&
        cont (put us (K - n) h)
          (put hs (K - n) (hull (Nat.lor (fld us (K - n)) h)))
          (put cs (K - n) a))) ||
      tryL K bc a h cont us hs cs n) = true
    by_cases e : K - j = n
    · have e2 : K - n = j := by omega
      rw [e2, h1, h2, h3]
      rfl
    · rw [ih hj (by omega)]
      exact Bool.or_true _

theorem orA_tb (q : ℕ) : ∀ (rest : List (ℕ × ℕ)), ∀ p ∈ rest, (fld p.1 0).testBit q = true →
    (orA (rest.map Prod.fst)).testBit q = true := by
  intro rest
  induction rest with
  | nil => intro p hp; simp at hp
  | cons r rest ih =>
    intro p hp hb
    show (Nat.lor (fld r.1 0) (orA (rest.map Prod.fst))).testBit q = true
    rw [tb_lor]
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [hb]; rfl
    · rw [ih p hp hb]; exact Bool.or_true _

theorem go_inv (K base : ℕ) (M : ℕ × ℕ → Prop)
    (h2 : ∀ i, 1 ≤ i → i ≤ K → ∀ q,
      (∃ U : ℕ, (∀ r, U.testBit r = true → ∃ p, M p ∧ p.2 = i ∧ (fld p.1 1).testBit r = true) ∧
        (hull U).testBit q = true) →
      base.testBit q = true ∨ ∃ p, M p ∧ 1 ≤ p.2 ∧ p.2 ≤ i ∧ (fld p.1 0).testBit q = true) :
    ∀ (rest : List (ℕ × ℕ)) (us hs cs : ℕ),
      (∀ p ∈ rest, M p) → (∀ p ∈ rest, p.2 ≤ K) →
      rest.Pairwise (fun p r => p.2 = r.2 → Nat.land (fld p.1 1) (fld r.1 1) = 0) →
      (∀ r ∈ rest, ∀ q, (fld us r.2).testBit q = true → (fld r.1 1).testBit q = true → False) →
      (∀ j q, (fld us j).testBit q = true → ∃ p, M p ∧ p.2 = j ∧ (fld p.1 1).testBit q = true) →
      (∀ j q, (fld hs j).testBit q = true →
        ∃ U : ℕ, (∀ r, U.testBit r = true → ∃ p, M p ∧ p.2 = j ∧ (fld p.1 1).testBit r = true) ∧
          (hull U).testBit q = true) →
      (∀ p, M p → p ∈ rest ∨ ∀ q, (fld p.1 0).testBit q = true → (fld cs p.2).testBit q = true) →
      go K base (rest.map Prod.fst) us hs cs = true := by
  intro rest
  induction rest with
  | nil => intro us hs cs _ _ _ _ _ _ _; rfl
  | cons it rest ih =>
    intro us hs cs hM hK hP Ius Ius2 Ihs Ics
    show tryL K (Nat.lor base (orA (rest.map Prod.fst))) (fld it.1 0) (fld it.1 1)
      (go K base (rest.map Prod.fst)) us hs cs (Nat.succ K) = true
    have hit : it ∈ it :: rest := List.mem_cons_self
    have bh : ∀ r, (fld it.1 1).testBit r = true → r < 144 := fun r => fld_lt _ _ r
    have ba : ∀ r, (fld it.1 0).testBit r = true → r < 144 := fun r => fld_lt _ _ r
    have bH : ∀ r, (hull (Nat.lor (fld us it.2) (fld it.1 1))).testBit r = true → r < 144 :=
      fun r hr => (hull_spec _ r hr).1
    have Fus : ∀ j q, (fld (put us it.2 (fld it.1 1)) j).testBit q = true →
        ∃ p, M p ∧ p.2 = j ∧ (fld p.1 1).testBit q = true := by
      intro j q hq
      by_cases hj : j = it.2
      · subst hj
        rw [fld_put_same _ _ _ _ bh, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact Ius2 _ q hq
        · exact ⟨it, hM it hit, rfl, hq⟩
      · rw [fld_put_ne _ _ _ _ _ bh hj] at hq
        exact Ius2 j q hq
    have Fhs : ∀ j q,
        (fld (put hs it.2 (hull (Nat.lor (fld us it.2) (fld it.1 1)))) j).testBit q = true →
        ∃ U : ℕ, (∀ r, U.testBit r = true → ∃ p, M p ∧ p.2 = j ∧ (fld p.1 1).testBit r = true) ∧
          (hull U).testBit q = true := by
      intro j q hq
      by_cases hj : j = it.2
      · subst hj
        rw [fld_put_same _ _ _ _ bH, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · exact Ihs _ q hq
        · refine ⟨Nat.lor (fld us it.2) (fld it.1 1), ?_, hq⟩
          intro r hr
          rw [tb_lor, Bool.or_eq_true] at hr
          rcases hr with hr | hr
          · exact Ius2 _ r hr
          · exact ⟨it, hM it hit, rfl, hr⟩
      · rw [fld_put_ne _ _ _ _ _ bH hj] at hq
        exact Ihs j q hq
    have Fcs : ∀ p, M p → p ∈ rest ∨
        ∀ q, (fld p.1 0).testBit q = true →
          (fld (put cs it.2 (fld it.1 0)) p.2).testBit q = true := by
      intro p hp
      have key : (∀ q, (fld p.1 0).testBit q = true → (fld cs p.2).testBit q = true) →
          ∀ q, (fld p.1 0).testBit q = true →
            (fld (put cs it.2 (fld it.1 0)) p.2).testBit q = true := by
        intro hold q hq
        by_cases hj : p.2 = it.2
        · rw [hj, fld_put_same _ _ _ _ ba, ← hj, hold q hq]
          rfl
        · rw [fld_put_ne _ _ _ _ _ ba hj]
          exact hold q hq
      rcases Ics p hp with hin | hold
      · rcases List.mem_cons.mp hin with rfl | hin
        · right
          intro q hq
          rw [fld_put_same _ _ _ _ ba, hq]
          exact Bool.or_true _
        · exact Or.inl hin
      · exact Or.inr (key hold)
    have hP' := List.pairwise_cons.mp hP
    apply tryL_true K _ _ _ _ us hs cs it.2 ?_ ?_ ?_ (Nat.succ K) (hK it hit)
      (Nat.lt_succ_of_le (Nat.sub_le _ _))
    · exact land_disj _ _ (Ius it hit)
    · apply chkA_true _ _ _ _ ?_ K 0 (Nat.le_refl _)
      · intro j hj1 hj2; omega
      · intro i hi1 hi2 q hq
        rcases h2 i hi1 hi2 q (Fhs i q hq) with hb | ⟨p, hp, hp1, hp2, hpq⟩
        · left
          rw [tb_lor, hb]
          rfl
        · rcases Fcs p hp with hin | hc
          · left
            rw [tb_lor, orA_tb q rest p hin hpq]
            exact Bool.or_true _
          · exact Or.inr ⟨p.2, hp1, hp2, hc q hpq⟩
    · apply ih _ _ _ (fun p hp => hM p (List.mem_cons_of_mem _ hp))
        (fun p hp => hK p (List.mem_cons_of_mem _ hp)) hP'.2 ?_ Fus Fhs Fcs
      intro r hr q hq hrq
      by_cases hj : r.2 = it.2
      · rw [hj, fld_put_same _ _ _ _ bh, Bool.or_eq_true] at hq
        rcases hq with hq | hq
        · rw [← hj] at hq
          exact Ius r (List.mem_cons_of_mem _ hr) q hq hrq
        · exact land_zero_tb _ _ q (hP'.1 r hr hj.symm) hq hrq
      · rw [fld_put_ne _ _ _ _ _ bh hj] at hq
        exact Ius r (List.mem_cons_of_mem _ hr) q hq hrq

theorem perm_map_lift {α β : Type} (f : α → β) {l1 l2 : List β} (h : l1.Perm l2) :
    ∀ ps : List α, ps.map f = l1 → ∃ ps' : List α, ps'.Perm ps ∧ ps'.map f = l2 := by
  induction h with
  | nil => intro ps hps; exact ⟨ps, List.Perm.refl _, hps⟩
  | cons x _ ih =>
    intro ps hps
    rcases ps with _ | ⟨p, ps⟩
    · simp at hps
    · rw [List.map_cons, List.cons.injEq] at hps
      obtain ⟨qs, hq1, hq2⟩ := ih ps hps.2
      refine ⟨p :: qs, List.Perm.cons p hq1, ?_⟩
      rw [List.map_cons, hq2, hps.1]
  | swap x y l =>
    intro ps hps
    rcases ps with _ | ⟨p, _ | ⟨q, r⟩⟩
    · simp at hps
    · rw [List.map_cons, List.cons.injEq] at hps
      simp at hps
    · rw [List.map_cons, List.map_cons, List.cons.injEq, List.cons.injEq] at hps
      refine ⟨q :: p :: r, List.Perm.swap _ _ _, ?_⟩
      rw [List.map_cons, List.map_cons, hps.1, hps.2.1, hps.2.2]
  | trans _ _ ih1 ih2 =>
    intro ps hps
    obtain ⟨qs, a, b⟩ := ih1 ps hps
    obtain ⟨rs, c, d⟩ := ih2 qs b
    exact ⟨rs, c.trans a, d⟩

theorem go_complete (K base : ℕ) (all : List (ℕ × ℕ)) (its : List ℕ)
    (hperm : its.Perm (all.map Prod.fst))
    (hK : ∀ p ∈ all, p.2 ≤ K)
    (h1 : all.Pairwise (fun p r => p.2 = r.2 → Nat.land (fld p.1 1) (fld r.1 1) = 0))
    (h2 : ∀ i, 1 ≤ i → i ≤ K → ∀ q,
      (∃ U : ℕ, (∀ r, U.testBit r = true →
          ∃ p, p ∈ all ∧ p.2 = i ∧ (fld p.1 1).testBit r = true) ∧
        (hull U).testBit q = true) →
      base.testBit q = true ∨
        ∃ p, p ∈ all ∧ 1 ≤ p.2 ∧ p.2 ≤ i ∧ (fld p.1 0).testBit q = true) :
    go K base its 0 0 0 = true := by
  obtain ⟨ps, hps, hmap⟩ := perm_map_lift Prod.fst hperm.symm all rfl
  rw [← hmap]
  have hsym : ∀ {p r : ℕ × ℕ}, (p.2 = r.2 → Nat.land (fld p.1 1) (fld r.1 1) = 0) →
      (r.2 = p.2 → Nat.land (fld r.1 1) (fld p.1 1) = 0) := by
    intro p r h e
    have h' := h e.symm
    apply land_disj
    intro q ha hb
    exact land_zero_tb _ _ q h' hb ha
  apply go_inv K base (fun p => p ∈ all) h2 ps 0 0 0
  · exact fun p hp => hps.mem_iff.mp hp
  · exact fun p hp => hK p (hps.mem_iff.mp hp)
  · exact (hps.pairwise_iff hsym).mpr h1
  · intro r _ q hq
    rw [fld_zero] at hq
    exact Bool.noConfusion hq
  · intro j q hq
    rw [fld_zero] at hq
    exact Bool.noConfusion hq
  · intro j q hq
    rw [fld_zero] at hq
    exact Bool.noConfusion hq
  · exact fun p hp => Or.inl (hps.mem_iff.mpr hp)

theorem vs_eq (t t2 : ℕ) : ∀ l : List ℕ, vs t t2 (l.map rectW) =
    (l.filter (fun x => !(Nat.beq (Nat.land (priv t (rectW x)) t2) 0))).map
      (fun x => put (Nat.land (rectW x) full) 1 (priv t (rectW x))) := by
  intro l
  induction l with
  | nil => rfl
  | cons x l ih =>
    show cond (Nat.beq (Nat.land (priv t (rectW x)) t2) 0) (vs t t2 (l.map rectW))
      (put (Nat.land (rectW x) full) 1 (priv t (rectW x)) :: vs t t2 (l.map rectW)) = _
    rw [ih]
    cases hb : Nat.beq (Nat.land (priv t (rectW x)) t2) 0
    · rw [List.filter_cons_of_pos (by rw [hb]; rfl)]
      rfl
    · rw [List.filter_cons_of_neg (by rw [hb]; exact Bool.noConfusion)]
      rfl

theorem fcov_tb (t t2 q : ℕ) : ∀ as : List ℕ, ∀ a ∈ as,
    Nat.beq (Nat.land (priv t a) t2) 0 = true → a.testBit q = true →
    (fcov t t2 as).testBit q = true := by
  intro as
  induction as with
  | nil => intro a ha; simp at ha
  | cons b as ih =>
    intro a ha hb hq
    show (cond (Nat.beq (Nat.land (priv t b) t2) 0) (Nat.lor b (fcov t t2 as))
      (fcov t t2 as)).testBit q = true
    rcases List.mem_cons.mp ha with rfl | ha
    · rw [hb]
      show (Nat.lor a (fcov t t2 as)).testBit q = true
      rw [tb_lor, hq]
      rfl
    · have := ih a ha hb hq
      cases Nat.beq (Nat.land (priv t b) t2) 0
      · exact this
      · show (Nat.lor b (fcov t t2 as)).testBit q = true
        rw [tb_lor, this]
        exact Bool.or_true _

theorem item_tb1 (a h q : ℕ) (hh : (fld (put (Nat.land a full) 1 h) 1).testBit q = true) :
    h.testBit q = true := by
  rw [fld_tb, put_tb, tb_land, full_tb] at hh
  have e : 144 * 1 + q - 144 * 1 = q := by omega
  have e1 : decide (144 * 1 + q < 144) = false := decide_eq_false (by omega)
  rw [e, e1, Bool.and_false, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true] at hh
  exact hh.1.2

theorem item_tb0 (a h q : ℕ) (hq : q < 144) (ha : a.testBit q = true) :
    (fld (put (Nat.land a full) 1 h) 0).testBit q = true := by
  rw [fld_tb, put_tb, tb_land, full_tb]
  have e : 144 * 0 + q = q := by omega
  rw [e, ha, decide_eq_true hq]
  rfl

theorem beq0_false {n : ℕ} (h : Nat.beq n 0 = false) : n ≠ 0 := by
  intro e
  rw [e] at h
  exact Bool.noConfusion h

theorem classP3_of_lab (K t t2 : ℕ) (l : List ℕ) (c : ℕ → ℕ)
    (hle : ∀ x ∈ l, Nat.land (priv t (rectW x)) t2 ≠ 0 → c x ≤ K)
    (hne : l.Pairwise (fun x y => Nat.land (priv t (rectW x)) t2 ≠ 0 →
      Nat.land (priv t (rectW y)) t2 ≠ 0 → c x = c y →
      Nat.land (priv t (rectW x)) (priv t (rectW y)) = 0))
    (hcov : ∀ i U : ℕ, 1 ≤ i → i ≤ K →
      (∀ r, U.testBit r = true → ∃ x ∈ l, Nat.land (priv t (rectW x)) t2 ≠ 0 ∧ c x = i ∧
        (priv t (rectW x)).testBit r = true) →
      ∀ q, (hull U).testBit q = true → ∃ y ∈ l, (rectW y).testBit q = true ∧
        (Nat.land (priv t (rectW y)) t2 ≠ 0 → 1 ≤ c y ∧ c y ≤ i)) :
    classP3 K t t2 (l.map rectW) = true := by
  have hmem : ∀ p : ℕ × ℕ,
      p ∈ (l.filter (fun x => !(Nat.beq (Nat.land (priv t (rectW x)) t2) 0))).map
        (fun x => (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x)) →
      ∃ x ∈ l, Nat.land (priv t (rectW x)) t2 ≠ 0 ∧
        p = (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x) := by
    intro p hp
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
    obtain ⟨hx1, hx2⟩ := List.mem_filter.mp hx
    refine ⟨x, hx1, ?_, rfl⟩
    apply beq0_false
    cases hb : Nat.beq (Nat.land (priv t (rectW x)) t2) 0
    · rfl
    · rw [hb] at hx2
      exact Bool.noConfusion hx2
  unfold classP3
  apply go_complete K _
    ((l.filter (fun x => !(Nat.beq (Nat.land (priv t (rectW x)) t2) 0))).map
      (fun x => (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x)))
  · have e : ((l.filter (fun x => !(Nat.beq (Nat.land (priv t (rectW x)) t2) 0))).map
        (fun x => (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x))).map Prod.fst =
        vs t t2 (l.map rectW) := by
      rw [vs_eq, List.map_map]
      rfl
    rw [e]
    cases Nat.blt 1 K
    · exact List.Perm.refl _
    · exact sortD_perm _ _
  · intro p hp
    obtain ⟨x, hx, hc, rfl⟩ := hmem p hp
    exact hle x hx hc
  · rw [List.pairwise_map]
    refine List.Pairwise.imp_of_mem ?_ (List.Pairwise.filter _ hne)
    intro x y hx hy hxy hc
    have hx' := hmem _ (List.mem_map_of_mem (f := fun x =>
      (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x)) hx)
    have hy' := hmem _ (List.mem_map_of_mem (f := fun x =>
      (put (Nat.land (rectW x) full) 1 (priv t (rectW x)), c x)) hy)
    obtain ⟨x', _, hcx, ex⟩ := hx'
    obtain ⟨y', _, hcy, ey⟩ := hy'
    have ex1 := congrArg Prod.fst ex
    have ey1 := congrArg Prod.fst ey
    have ex2 := congrArg Prod.snd ex
    have ey2 := congrArg Prod.snd ey
    have hcx' : Nat.land (priv t (rectW x)) t2 ≠ 0 := by
      have hx2 := (List.mem_filter.mp hx).2
      apply beq0_false
      cases hb : Nat.beq (Nat.land (priv t (rectW x)) t2) 0
      · rfl
      · rw [hb] at hx2
        exact Bool.noConfusion hx2
    have hcy' : Nat.land (priv t (rectW y)) t2 ≠ 0 := by
      have hy2 := (List.mem_filter.mp hy).2
      apply beq0_false
      cases hb : Nat.beq (Nat.land (priv t (rectW y)) t2) 0
      · rfl
      · rw [hb] at hy2
        exact Bool.noConfusion hy2
    have h0 := hxy hcx' hcy' hc
    apply land_disj
    intro q ha hb
    exact land_zero_tb _ _ q h0 (item_tb1 _ _ q ha) (item_tb1 _ _ q hb)
  · intro i hi1 hi2 q hq
    obtain ⟨U, hU, hUq⟩ := hq
    have hq144 : q < 144 := (hull_spec U q hUq).1
    obtain ⟨y, hy, hyq, hyc⟩ := hcov i U hi1 hi2 (by
      intro r hr
      obtain ⟨p, hp, hpi, hpr⟩ := hU r hr
      obtain ⟨x, hx, hc, rfl⟩ := hmem p hp
      exact ⟨x, hx, hc, hpi, item_tb1 _ _ r hpr⟩) q hUq
    cases hb : Nat.beq (Nat.land (priv t (rectW y)) t2) 0
    · right
      have hc := hyc (beq0_false hb)
      refine ⟨(put (Nat.land (rectW y) full) 1 (priv t (rectW y)), c y), ?_, hc.1, hc.2,
        item_tb0 _ _ q hq144 hyq⟩
      apply List.mem_map_of_mem
      apply List.mem_filter.mpr
      refine ⟨hy, ?_⟩
      rw [hb]
      rfl
    · left
      exact fcov_tb t t2 q _ (rectW y) (List.mem_map_of_mem hy) hb hyq

theorem classP_of_classLab (l : List ℕ) (k : ℕ) (c : ℕ → ℕ)
    (h : ClassLab l (Nat.sub (Nat.succ k) l.length) c) : classP l k = true :=
  classP3_of_lab _ _ _ l c h.le h.ne h.cov

theorem classP_of_validLab (l : List ℕ) (k : ℕ) (c : ℕ → ℕ) (hnd : l.Nodup)
    (h : ValidLab l (Nat.sub (Nat.succ k) l.length) c) : classP l k = true :=
  classP_of_classLab l k c (h.classLab hnd)

theorem classP'_of_validLab (l : List ℕ) (k : ℕ) (c : ℕ → ℕ) (hnd : l.Nodup)
    (h : ValidLab l (Nat.sub (Nat.succ k) l.length) c) : classP' l k = true := by
  rw [classP'_eq]
  exact classP_of_validLab l k c hnd h


theorem reachMore {m : Bool} {S : Finset Nat} {k : Nat} (h : Reach m S k) : Reach m S (k+1) := by
  induction h using Reach.ind with
  | done k => exact Or.inl rfl
  | step D k u v w ka kb hu hv gate hd hb tail ih =>
    exact Or.inr ⟨u,v,w,ka,kb,hu,hv,gate,hd,hb,ih⟩

theorem reachPad {m : Bool} {S : Finset Nat} {k cap : Nat}
    (le : k ≤ cap) (h : Reach m S k) : Reach m S cap := by
  induction le with
  | refl => exact h
  | step _ ih => exact reachMore ih

def forceWord (w : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (k 0) (fun n _ => k (n + 1)) w

theorem forceWordEq (w : Nat) (k : Nat → Bool) : forceWord w k = k w := by
  cases w <;> rfl

def forceColumns (ws : List Nat) (k : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun f => f [])
    (fun a _ next f => forceWord a (fun w => next (fun tail => f (w :: tail)))) ws) k

theorem forceColumnsEq (ws : List Nat) (k : List Nat → Bool) : forceColumns ws k = k ws := by
  induction ws generalizing k with
  | nil => rfl
  | cons a ws ih =>
    change forceWord a (fun w => forceColumns ws (fun tail => k (w :: tail))) = _
    rw [forceWordEq, ih]

def tryFast (K base a h : Nat) (cont : Nat → Nat → Nat → Bool)
    (us hs cs n : Nat) : Bool :=
  Nat.rec false (fun i more =>
    let j := K - i
    forceWord (fld us j) (fun old =>
      if Nat.beq (old &&& h) 0 then
        forceWord (hull (old ||| h)) (fun box =>
          forceWord (put hs j box) (fun boxes =>
            forceWord (put cs j a) (fun covered =>
              (chkA' base boxes covered K K 0 && cont (put us j h) boxes covered) || more)))
      else more)) n

theorem tryFastEq (K base a h : Nat) (cont : Nat → Nat → Nat → Bool)
    (us hs cs n : Nat) : tryFast K base a h cont us hs cs n = tryL' K base a h cont us hs cs n := by
  induction n with
  | zero => rfl
  | succ i ih =>
    let j := K-i
    let old := fld us j
    let box := hull (old ||| h)
    let boxes := put hs j box
    let covered := put cs j a
    change forceWord old (fun prev => if Nat.beq (prev &&& h) 0 then
      forceWord (hull (prev ||| h)) (fun shape =>
        forceWord (put hs j shape) (fun saved =>
          forceWord covered (fun bank =>
            (chkA' base saved bank K K 0 && cont (put us j h) saved bank) ||
              tryFast K base a h cont us hs cs i))) else tryFast K base a h cont us hs cs i)
      = bor (band (Nat.beq (old &&& h) 0)
        (band (chkA' base boxes covered K K 0) (cont (put us j h) boxes covered)))
        (tryL' K base a h cont us hs cs i)
    simp only [forceWordEq, ih, bor_eq, band_eq]
    cases Nat.beq (old &&& h) 0 <;> rfl

def goFast (K base : Nat) (items : List Nat) : Nat → Nat → Nat → Bool :=
  List.rec (fun _ _ _ => true)
    (fun item rest run us hs cs =>
      forceWord (base ||| orA' rest) (fun cover =>
        tryFast K cover (fld item 0) (fld item 1) run us hs cs (K+1))) items

theorem goFastEq (K base : Nat) (items : List Nat) : goFast K base items = go' K base items := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    funext us hs cs
    change forceWord (base ||| orA' rest) (fun cover =>
      tryFast K cover (fld item 0) (fld item 1) (goFast K base rest) us hs cs (K+1)) =
      tryL' K (base ||| orA' rest) (fld item 0) (fld item 1) (go' K base rest) us hs cs (K+1)
    rw [forceWordEq, tryFastEq, ih]

def classQFast (K : Nat) (as : List Nat) : Bool :=
  forceWord (tw' as 0 0) fun t =>
    forceColumns (mapP' t as) fun ps =>
      forceWord (tw' ps 0 0) fun t2 =>
        forceColumns (vs' t t2 as) fun items =>
          forceWord (fcov' t t2 as) fun cover =>
            goFast K cover (cond (Nat.blt 1 K) (sortD' items items) items) 0 0 0

theorem classQFastEq (K : Nat) (as : List Nat) : classQFast K as = classQ K as := by
  simp only [classQFast, forceWordEq, forceColumnsEq, goFastEq, classQ]
  cases Nat.blt 1 K <;> rfl

def forceClass (ws : List Nat) (fuel : Nat) : Bool :=
  forceColumns (mapW' ws) (classQFast (fuel + 1 - ws.length))

theorem forceClassEq (ws : List Nat) (fuel : Nat) : forceClass ws fuel = classP' ws fuel := by
  simp only [forceClass, forceColumnsEq, classQFastEq, classP']
  rfl

noncomputable def packedClassTerm : {f : List Nat → Nat → Bool // f = forceClass} := by
  refine ⟨?f, ?proof⟩
  case proof =>
    delta forceClass classQFast forceColumns forceWord goFast tryFast chkA' fld put subM hull hullC rowsOf colsOf orS orSL rowM full
      band bor bnot vs' fcov' priv tw' mapP' mapW' rectW' rectRowMask rectRepeat rect' tb' orA' sortD' insD' degI'
    beta_reduce
    exact rfl

noncomputable def packedClass : List Nat → Nat → Bool := packedClassTerm.1

theorem packedClassEq : packedClass = classP' := by
  unfold packedClass
  rw [packedClassTerm.2]
  funext ws fuel
  exact forceClassEq ws fuel

def orFast (ws : List Nat) : Nat :=
  List.rec 0 (fun w _ acc => rectW' w ||| acc) ws

theorem orFastEq (ws : List Nat) : orFast ws = orR ws := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change rectW' w ||| orFast ws = rectW w ||| orR ws
    rw [rectW'_eq, ih]

def fastRectColumn (ws : List Nat) : Bool :=
  forceColumns (mapW' ws) fun rs =>
    forceWord (tw' rs 0 0) fun twice => hullsOK' twice rs 0

theorem fastRectColumnEq (ws : List Nat) : fastRectColumn ws = rectOK1 ws := by
  simp only [fastRectColumn, forceColumnsEq, forceWordEq, mapW'_eq, hullsOK'_eq, tw'_eq, rectOK1, avOK1]

noncomputable def fastRectTerm : {f : List Nat → Bool // f = fastRectColumn} := by
  refine ⟨?algorithm, ?proof⟩
  case proof =>
    delta fastRectColumn forceColumns forceWord mapW' hullsOK' tw' priv hull hullC rowsOf colsOf orS orSL rowM full rectW'
      rect' tb' band bor bnot
    beta_reduce
    exact rfl

noncomputable def fastRect := fastRectTerm.1

theorem fastRectEq (ws : List Nat) : fastRect ws = rectOK1 ws :=
  congrFun fastRectTerm.2 ws |>.trans (fastRectColumnEq ws)

end PackedRect

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

def MonoAuto (target : Nat) (stock : List Nat) (map : Fin rows → Fin rows) : Prop :=
  Function.Surjective map ∧ relabel map target = target ∧
    stock.toFinset.image (relabel map) = stock.toFinset

theorem monoImage {map : Fin rows → Fin rows} {target : Nat} {stock : List Nat}
    (auto : MonoAuto target stock map) (stockMasked : ∀ w ∈ stock, Masked (fullMask rows) w)
    {k : Nat} {S : Finset Nat}
    (stateMasked : ∀ w ∈ S, Masked (fullMask rows) w)
    (run : MonoPlan false (fullMask rows) target stock k S) :
    MonoPlan false (fullMask rows) target stock k (S.image (relabel map)) := by
  let f := relabel map
  have inj {a b : Nat} (ha : Masked (fullMask rows) a) (hb : Masked (fullMask rows) b) :
      f a = f b → a = b := relabelInj map auto.1 ha hb
  have maskConst : Masked (fullMask rows) (fullMask rows) := by simp [Masked]
  have zeroConst : Masked (fullMask rows) 0 := by simp [Masked]
  have proper {w : Nat} (hm : Masked (fullMask rows) w) (hp : properWord (fullMask rows) w) :
      properWord (fullMask rows) (f w) := by
    refine ⟨fun h => hp.1 (inj hm zeroConst (h.trans (relabelZero map).symm)),
      fun h => hp.2 (inj hm maskConst (h.trans (relabelMask map).symm))⟩
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hp⟩ := run
    change (Finset.image f {target}) = {target} ∧ _
    rw [Finset.image_singleton, show f target = target from auto.2.1]
    exact ⟨rfl, hp⟩
  | succ k ih =>
    obtain ⟨U,a,b,op,rfl,pa,pb,ab,fresh,old,_,tail⟩ := run
    let v := binWord op a b
    have ma := stateMasked a (Finset.mem_insert_self ..)
    have mb := stateMasked b (Finset.mem_insert_of_mem (Finset.mem_insert_self ..))
    have mv : Masked (fullMask rows) v := by
      have av : ∀ w ∈ [a,b], Masked (fullMask rows) w := by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro w (rfl | rfl) <;> assumption
      apply maskedGate av
      exact Or.inr ⟨a,b,Or.inr (Or.inr (by simp)),Or.inr (Or.inr (by simp)),by
        cases op <;> simp [v, binWord]⟩
    have childMasked : ∀ w ∈ insert v U, Masked (fullMask rows) w := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hU
      · exact mv
      · exact stateMasked _ (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU))
    have mapV : f v = binWord op (f a) (f b) := by
      cases op
      · exact relabelAnd ..
      · exact relabelOr ..
    have freshMap : f v ∉ (insert a (insert b U)).image f := by
      intro hh
      obtain ⟨w, hw, hEq⟩ := Finset.mem_image.mp hh
      have eq := inj (stateMasked _ hw) mv hEq
      change v ∉ _ at fresh
      exact fresh (eq ▸ hw)
    have oldMap : f v ∉ stock := by
      intro hm
      have he : f v ∈ stock.toFinset.image f := by
        rw [auto.2.2]
        exact List.mem_toFinset.mpr hm
      obtain ⟨w, hw, eq⟩ := Finset.mem_image.mp he
      have wm := List.mem_toFinset.mp hw
      have heq := inj (stockMasked _ wm) mv eq
      change v ∉ stock at old
      exact old (heq ▸ wm)
    have next := ih childMasked tail
    change MonoPlan false (fullMask rows) target stock (k+1) ((insert a (insert b U)).image f)
    refine ⟨U.image f,f a,f b,op,by simp only [Finset.image_insert],proper ma pa,proper mb pb,
      fun h => ab (inj ma mb h),?_,?_,by simp [DominanceRule],?_⟩
    · rwa [← mapV]
    · rwa [← mapV]
    · rw [Finset.image_insert] at next
      change MonoPlan false (fullMask rows) target stock k (insert (f v) (U.image f)) at next
      rw [mapV] at next
      exact next


def KWAuto (target : Nat) (stock : List Nat) (move : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24))) : Prop :=
  MonoAuto target stock move.2 ∧
    ∀ w, Masked (fullMask 24) w → mixMove move.1 w = relabel move.2 w

def imageWords (move : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24))) (ws : List Nat) : List Nat :=
  List.rec [] (fun w _ next => insertWord (mixMove move.1 w) next) ws

theorem imageWordsSet (move : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24))) (ws : List Nat)
    (agree : ∀ w ∈ ws, mixMove move.1 w = relabel move.2 w) :
    (imageWords move ws).toFinset = ws.toFinset.image (relabel move.2) := by
  induction ws with
  | nil => simp [imageWords]
  | cons w ws ih =>
    change (insertWord (mixMove move.1 w) (imageWords move ws)).toFinset = _
    rw [insertWordSet, ih (fun w h => agree w (List.mem_cons_of_mem _ h)),
      agree w (by simp), List.toFinset_cons, Finset.image_insert]

def kwMove (fuel : Nat) (ws : List Nat) (x y w : Nat) (keep : Nat) : (Nat × List Nat × List (Nat × Nat × Nat)) :=
  (fuel - 1, insertWord w (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws)), [(w,x,y)])

theorem binaryTransition {mask fuel : Nat} {x y : Nat} {d : Bool} {U : Finset Nat}
    {ws : List Nat} {history : List (Nat × Nat × Nat)}
    (nd : ws.Nodup) (wide : ws.length ≤ 64) (hf : fuel ≠ 0)
    (he : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
    (ordered : ws.idxOf x < ws.idxOf y) (fresh : binWord d x y ∉ insert x (insert y U))
    (p : properWord mask (binWord d x y)) :
    ∃ a b keep child, a < b ∧ b < ws.length ∧ keep < 4 ∧
      childState mask (gateToken a b (if d then 1 else 0) keep) (fuel, ws, history) = some child ∧
      ws.getD a 0 = x ∧ ws.getD b 0 = y ∧ child.2.1 = (kwMove fuel ws x y (binWord d x y) keep).2.1 ∧
      child.1 = fuel - 1 ∧ child.2.2.head?.map Prod.fst = some (binWord d x y) ∧ child.2.1.Nodup ∧ child.2.1.toFinset = insert (binWord d x y) U := by
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
  refine ⟨a, b, keep, child, hab, hb, keepLt, ?_, ?_⟩
  · have eq := binaryChild (fuel := fuel) (history := history) d hab hb (by omega) hf keepLt hx hy p fn
    rw [bx, by'] at eq
    exact eq
  · refine ⟨hx, hy, by simp [child, kwMove, rest, v, bx, by'], rfl, rfl, insertWordNodup (keepNodup (keepNodup nd saveX x) saveY y)
      (fun h => fn (keepSubset saveX x ws _ (keepSubset saveY y _ _ h))), ?_⟩
    change (insertWord v rest).toFinset = insert v U
    rw [insertWordSet, keepPairSet nd xy he]

theorem monoPlanPacked {enabled : Bool} {stock : List Nat} {k : Nat} {S : Finset Nat}
    (h : MonoPlan enabled 16777215 4095 stock k S) :
    PackedRect.Reach false S k := by
  induction k generalizing S with
  | zero => exact h.1
  | succ k ih =>
    obtain ⟨U,a,b,op,eq,pa,pb,ab,fresh,old,rule,tail⟩ := h
    have allowed : ∀ d ∈ S, PackedRect.blk false (binWord op a b) d = false := by
      intro d hd
      apply Bool.eq_false_iff.mpr
      intro h
      have e : binWord op a b = d := by simpa [PackedRect.blk] using h
      exact fresh (e.symm ▸ hd)
    have ha : a ∈ S := by rw [eq]; simp
    have hb : b ∈ S := by rw [eq]; simp
    have opEq : binWord op a b = a &&& b ∨ binWord op a b = a ||| b := by
      cases op <;> simp [binWord]
    apply Or.inr
    refine ⟨a,b,binWord op a b,decide (a ∈ U),decide (b ∈ U),ha,hb,opEq,allowed,trivial,?_⟩
    rw [keepFilterEq ab eq]
    exact ih tail

theorem packedValidClass {enabled : Bool} {stock ws : List Nat} {k fuel : Nat}
    (nd : ws.Nodup) (cap : k ≤ fuel)
    (plan : MonoPlan enabled 16777215 4095 stock k ws.toFinset) :
    PackedRect.covR (PackedRect.orR ws) = true ∧
      (if ws.length == fuel + 1 then PackedRect.rectOK1 ws else PackedRect.classP' ws fuel) = true := by
  have packed := monoPlanPacked plan
  have grow : PackedRect.Reach false ws.toFinset fuel := by
    exact PackedRect.reachPad cap packed
  have cover : PackedRect.covR (PackedRect.orR ws) = true := by
    cases h : PackedRect.covR (PackedRect.orR ws)
    · exact False.elim (PackedRect.cover_sound h grow)
    · rfl
  refine ⟨cover, ?_⟩
  by_cases hlen : ws.length = fuel + 1
  · simp [hlen, PackedRect.rectOK1_sound nd hlen grow]
  · obtain ⟨c, hc⟩ := PackedRect.reach_validLab nd grow
    simp [hlen, PackedRect.classP'_of_validLab _ _ c nd hc]

def MonoViable (enabled : Bool) (mask target : Nat) (stock : List Nat) (state : (Nat × List Nat × List (Nat × Nat × Nat))) : Prop :=
  state.2.1.Nodup ∧ (∀ w ∈ state.2.1, Masked mask w) ∧
    ∃ k, k ≤ state.1 ∧ MonoPlan enabled mask target stock k state.2.1.toFinset

def monoBlocked (dom : Bool) (mask target : Nat) (stock : List Nat) (state child : (Nat × List Nat × List (Nat × Nat × Nat))) : Bool :=
  match child.2.2.head? with
  | none => true
  | some (w, _, _) =>
    stock.contains w || (dom && (dominanceB mask target 0 w || dominanceB mask target mask w ||
      (state.2.1 ++ stock).any (fun d => dominanceB mask target d w)))

theorem monoBlockedClear {dom : Bool} {stock : List Nat} {state child : (Nat × List Nat × List (Nat × Nat × Nat))}
    {w : Nat} (value : child.2.2.head?.map Prod.fst = some w) (fresh : w ∉ stock)
    (rule : DominanceRule dom mask target stock state.2.1.toFinset w) :
    monoBlocked dom mask target stock state child = false := by
  cases eq : child.2.2.head? with
  | none => simp [eq] at value
  | some recipe =>
    unfold monoBlocked
    rw [eq]
    obtain ⟨v,a,b⟩ := recipe
    have ev : v = w := by simpa [eq] using value
    subst v
    have absent : stock.contains w = false := by simpa using fresh
    change (stock.contains w || _) = false
    rw [absent, Bool.false_or]
    cases enabled : dom
    · rfl
    have zero : dominanceB mask target 0 w = false :=
      Bool.eq_false_iff.mpr (fun h => rule enabled _ (Or.inr (Or.inl rfl)) (dominanceB_spec.mp h))
    have one : dominanceB mask target mask w = false :=
      Bool.eq_false_iff.mpr (fun h => rule enabled _ (Or.inr (Or.inr (Or.inl rfl))) (dominanceB_spec.mp h))
    have bank : (state.2.1 ++ stock).any (fun d => dominanceB mask target d w) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      obtain ⟨d, hd, dc⟩ := List.any_eq_true.mp h
      rcases List.mem_append.mp hd with hl | hs
      · exact rule enabled d (Or.inl (List.mem_toFinset.mpr hl)) (dominanceB_spec.mp dc)
      · exact rule enabled d (Or.inr (Or.inr (Or.inr hs))) (dominanceB_spec.mp dc)
    simp [enabled, zero, one, bank]

theorem monoProgress {dom : Bool} {stock : List Nat} {state : (Nat × List Nat × List (Nat × Nat × Nat))}
    (width : state.2.1.length ≤ 64) (h : MonoViable dom mask target stock state) :
    target ∈ state.2.1 ∨ ∃ a b op keep child, a < b ∧ b < state.2.1.length ∧ op < 2 ∧ keep < 4 ∧
      childState mask (gateToken a b op keep) state = some child ∧
      monoBlocked dom mask target stock state child = false ∧
      let x := state.2.1.getD a 0
      let y := state.2.1.getD b 0
      let w := if op == 0 then x &&& y else x ||| y
      properWord mask w ∧ w ∉ state.2.1 ∧ w ∉ stock ∧
      child.2.1 = (kwMove state.1 state.2.1 x y w keep).2.1 ∧
      child.1 = state.1 - 1 ∧ MonoViable dom mask target stock child := by
  obtain ⟨fuel,ws,history⟩ := state
  obtain ⟨nd, masked, k, cap, plan⟩ := h
  cases k with
  | zero =>
    exact Or.inl (List.mem_toFinset.mp (by rw [plan.1]; simp))
  | succ k =>
    right
    obtain ⟨U,x,y,d,he,px,py,xy,fresh,old,rule,tail⟩ := plan
    have xm : x ∈ ws := by rw [← List.mem_toFinset, he]; simp
    have ym : y ∈ ws := by rw [← List.mem_toFinset, he]; simp
    have ne : ws.idxOf x ≠ ws.idxOf y := by
      intro h
      apply xy
      rw [← getWord xm, h, getWord ym]
    have advance {x y : Nat} (eq : ws.toFinset = insert x (insert y U)) (xy : x ≠ y)
        (ordered : ws.idxOf x < ws.idxOf y) (fresh : binWord d x y ∉ ws.toFinset)
        (old : binWord d x y ∉ stock) (rule : DominanceRule dom mask target stock ws.toFinset (binWord d x y))
        (tail : MonoPlan dom mask target stock k (insert (binWord d x y) U)) :
        ∃ a b op keep child, a < b ∧ b < ws.length ∧ op < 2 ∧ keep < 4 ∧
          childState mask (gateToken a b op keep) (fuel, ws, history) = some child ∧
          monoBlocked dom mask target stock (fuel, ws, history) child = false ∧
          let left := ws.getD a 0
          let right := ws.getD b 0
          let w := if op == 0 then left &&& right else left ||| right
          properWord mask w ∧ w ∉ ws ∧ w ∉ stock ∧
          child.2.1 = (kwMove fuel ws left right w keep).2.1 ∧
          child.1 = fuel - 1 ∧ MonoViable dom mask target stock child := by
      have pf := liveWordProper (monoPlanLive tail) _ (Finset.mem_insert_self ..)
      have hf : fuel ≠ 0 := by change k + 1 ≤ fuel at cap; omega
      obtain ⟨a,b,keep,child,hab,hb,hk,eval,hx,hy,words,budget,val,nodup,childSet⟩ :=
        binaryTransition (fuel := fuel) (history := history) nd width hf eq xy ordered (by simpa only [← eq] using fresh) pf
      refine ⟨a,b,if d then 1 else 0,keep,child,hab,hb,by cases d <;> decide,hk,eval,
        monoBlockedClear val old rule,?_,?_,?_,?_,budget,nodup,?_,k,?_,?_⟩
      · simp only [hx,hy]; cases d <;> exact pf
      · simp only [hx,hy,← List.mem_toFinset]; cases d <;> exact fresh
      · simp only [hx,hy]; cases d <;> exact old
      · simp only [hx,hy]; cases d <;> exact words
      · intro w hw
        have hm := List.mem_toFinset.mpr hw
        rw [childSet] at hm
        rcases Finset.mem_insert.mp hm with rfl | hU
        · have av : ∀ w ∈ ws, Masked mask w := masked
          apply maskedGate av
          have hx : x ∈ ws := by rw [← List.mem_toFinset,eq]; simp
          have hy : y ∈ ws := by rw [← List.mem_toFinset,eq]; simp
          exact Or.inr ⟨x,y,Or.inr (Or.inr hx),Or.inr (Or.inr hy),by cases d <;> simp [binWord]⟩
        · apply masked
          rw [← List.mem_toFinset, eq]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU)
      · rw [budget]
        change k + 1 ≤ fuel at cap
        omega
      · rwa [childSet]
    by_cases order : ws.idxOf x < ws.idxOf y
    · exact advance he xy order fresh old rule tail
    · apply advance (x := y) (y := x)
      · rw [he, Finset.insert_comm]
      · exact xy.symm
      · omega
      · simpa only [binWord_comm d y x] using fresh
      · simpa only [binWord_comm d y x] using old
      · simpa only [binWord_comm d y x] using rule
      · simpa only [binWord_comm d y x] using tail

def kwTableSize (table : (Nat × Nat × (Nat → List Nat))) : Nat := table.1

def unpackKW (dictionary fieldBits width word : Nat) : List Nat :=
  (Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun i next data =>
      let slot := unpack data fieldBits i
      if slot == 0 then [] else unpack dictionary 24 (slot-1) :: next data) width) word

def packKW (width : Nat) (ws : List Nat) : Nat :=
  let packed := (List.rec (motive := fun _ => Nat → Nat) id
    (fun w _ next acc => next ((acc <<< 24) ||| w)) ws) 0
  packed <<< (24 * (width - ws.length))

def kwLookup (table : (Nat × Nat × (Nat → List Nat))) (i : Nat) : Option (List Nat) :=
  if i < kwTableSize table then some (table.2.2 i) else none

theorem kwLookupInside {table : (Nat × Nat × (Nat → List Nat))} {i : Nat} {ws : List Nat}
    (lookup : kwLookup table i = some ws) : i < kwTableSize table := by
  by_contra! h
  simp [kwLookup, Nat.not_lt.mpr h] at lookup

def kwWordsEq (a b : List Nat) : Bool :=
  (List.rec (motive := fun _ => List Nat → Bool)
    (fun ys => List.rec true (fun _ _ _ => false) ys)
    (fun x _ next ys => List.rec false (fun y tail _ => Nat.beq x y && next tail) ys) a) b

theorem kwWordsEqSpec {a b : List Nat} (h : kwWordsEq a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [kwWordsEq]
  | cons x xs ih =>
    cases b with
    | nil => contradiction
    | cons y ys =>
      change (Nat.beq x y && kwWordsEq xs ys) = true at h
      obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp h
      rw [Nat.beq_eq.mp head, ih tail]

def kwSearch (entries : (Nat × Nat × (Nat → List Nat))) (key : List Nat) (limit lo hi : Nat) : Bool :=
  let packed := packKW entries.2.1 key
  (Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun _ next lo hi =>
      if Nat.blt lo hi then
        let mid := (lo + hi) / 2
        let stored := packKW entries.2.1 (entries.2.2 mid)
        if Nat.beq packed stored then
          match kwLookup entries mid with
          | none => false
          | some ws => kwWordsEq key ws
        else if Nat.blt packed stored then next lo mid else next (mid + 1) hi
      else false) limit) lo hi

def kwFind (entries : (Nat × Nat × (Nat → List Nat))) (key : List Nat) : Bool :=
  kwSearch entries key (entries.1.log2 + 2) 0 entries.1

theorem kwSearchSpec {entries : (Nat × Nat × (Nat → List Nat))} {key : List Nat} {limit lo hi : Nat}
    (ok : kwSearch entries key limit lo hi = true) : ∃ i : Nat, kwLookup entries i = some key := by
  induction limit generalizing lo hi with
  | zero => contradiction
  | succ limit ih =>
    let mid := (lo + hi) / 2
    let stored := packKW entries.2.1 (entries.2.2 mid)
    let packed := packKW entries.2.1 key
    change (if Nat.blt lo hi then
        if Nat.beq packed stored then
          match kwLookup entries mid with
          | none => false
          | some ws => kwWordsEq key ws
        else if Nat.blt packed stored then kwSearch entries key limit lo mid
          else kwSearch entries key limit (mid + 1) hi
      else false) = true at ok
    split at ok
    · split at ok
      · split at ok
        · contradiction
        next ws entry =>
          have eq : key = ws := kwWordsEqSpec ok
          exact ⟨mid, by rwa [eq]⟩
      · split at ok <;> exact ih ok
    · contradiction

theorem kwFindSpec {entries : (Nat × Nat × (Nat → List Nat))} {key : List Nat} (ok : kwFind entries key = true) :
    ∃ i : Nat, kwLookup entries i = some key := kwSearchSpec ok

def kwReferences (maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24))) (entries memo : (Nat × Nat × (Nat → List Nat))) (ws : List Nat) : Bool :=
  (kwFind entries ws || kwFind memo ws) ||
    maps.any (fun f => let image := imageWords f ws; kwFind entries image || kwFind memo image)


def kwHintFind (packed budget lo hi token : Nat) : Nat :=
  (Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0)
    (fun _ next first endAt =>
      if Nat.blt first endAt then
        let mid := (first + endAt) / 2
        let entry := (packed >>> (34 * mid)) &&& ((1 <<< 34) - 1)
        let code := entry >>> 18
        if Nat.beq code token then entry &&& ((1 <<< 18) - 1)
        else if Nat.blt token code then next first mid else next (mid + 1) endAt
      else 0) budget) lo hi

def kwHintLookup (maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24))) (entries memo : (Nat × Nat × (Nat → List Nat)))
    (ws : List Nat) (hint : Nat) : Bool :=
  if hint == 0 then false
  else
    let code := hint - 1
    let table := if (code / 16) % 2 == 0 then entries else memo
    match kwLookup table (code / 32) with
    | none => false
    | some stored =>
      let transform := code % 16
      if transform == 0 then kwWordsEq ws stored
      else
        match maps[transform - 1]? with
        | none => false
        | some f => kwWordsEq (imageWords f ws) stored

theorem kwHintSpec {maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24))} {entries memo : (Nat × Nat × (Nat → List Nat))}
    {ws : List Nat} {hint : Nat} (ok : kwHintLookup maps entries memo ws hint = true) :
    ∃ key i, (kwLookup entries i = some key ∨ kwLookup memo i = some key) ∧
      (key = ws ∨ ∃ f ∈ maps, key = imageWords f ws) := by
  unfold kwHintLookup at ok
  split at ok
  · contradiction
  next good =>
    let index := (hint - 1) / 32
    let table := if (hint - 1) / 16 % 2 == 0 then entries else memo
    change (match kwLookup table index with
      | none => false
      | some stored =>
        if (hint - 1) % 16 == 0 then kwWordsEq ws stored
        else match maps[(hint - 1) % 16 - 1]? with
             | none => false
             | some f => kwWordsEq (imageWords f ws) stored) = true at ok
    split at ok
    · contradiction
    next stored found =>
      have member : kwLookup entries index = some stored ∨ kwLookup memo index = some stored := by
        unfold table at found
        split at found
        · exact Or.inl found
        · exact Or.inr found
      refine ⟨stored,index,member,?_⟩
      split at ok
      · exact Or.inl (kwWordsEqSpec ok).symm
      · split at ok
        · contradiction
        next f hf =>
          exact Or.inr ⟨f,List.mem_of_getElem? hf,(kwWordsEqSpec ok).symm⟩

def kwReferenceCheck (maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24))) (entries memo : (Nat × Nat × (Nat → List Nat)))
    (ws : List Nat) (hint : Option Nat) : Bool :=
  match hint with
  | none => kwReferences maps entries memo ws
  | some code => kwHintLookup maps entries memo ws code

theorem kwReferenceSpec {maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24))} {entries memo : (Nat × Nat × (Nat → List Nat))}
    {ws : List Nat} {hint : Option Nat}
    (ok : kwReferenceCheck maps entries memo ws hint = true) :
    ∃ key i, (kwLookup entries i = some key ∨ kwLookup memo i = some key) ∧
      (key = ws ∨ ∃ f ∈ maps, key = imageWords f ws) := by
  cases hint with
  | some code => exact kwHintSpec ok
  | none =>
    have ref {key : List Nat} (lookup : (kwFind entries key || kwFind memo key) = true) :
        ∃ i, kwLookup entries i = some key ∨ kwLookup memo i = some key := by
      rcases Bool.or_eq_true_iff.mp lookup with he | hm
      · obtain ⟨i,hi⟩ := kwFindSpec he; exact ⟨i,Or.inl hi⟩
      · obtain ⟨i,hi⟩ := kwFindSpec hm; exact ⟨i,Or.inr hi⟩
    rcases Bool.or_eq_true_iff.mp ok with base | image
    · obtain ⟨i,hi⟩ := ref base
      exact ⟨ws,i,hi,Or.inl rfl⟩
    · obtain ⟨f,hf,hm⟩ := List.any_eq_true.mp image
      obtain ⟨i,hi⟩ := ref hm
      exact ⟨_,i,hi,Or.inr ⟨f,hf,rfl⟩⟩

noncomputable def kwColor (fuel : Nat) (ws : List Nat) : Bool :=
  if ws.length == fuel + 1 then PackedRect.fastRect ws else PackedRect.packedClass ws fuel

noncomputable def kwPruned (fuel : Nat) (ws : List Nat) : Bool :=
  ws.length > fuel + 1 || !kwColor fuel ws || !PackedRect.covR (PackedRect.orFast ws)

noncomputable def kwClosed (maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24)))
    (entries memo : (Nat × Nat × (Nat → List Nat))) (state : (Nat × List Nat × List (Nat × Nat × Nat))) (hint : Option Nat := none) : Bool :=
  let (fuel, ws, _) := state
  ws.length > fuel + 1 || !PackedRect.covR (PackedRect.orFast ws) ||
    (!ws.contains 4095 && (fuel == 0 || kwReferenceCheck maps entries memo ws hint || !kwColor fuel ws))

def kwSortedAfter (previous : Nat) (ws : List Nat) : Bool :=
  (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ next prior => Nat.blt prior w && next w) ws) previous

theorem kwSortedSpec {previous : Nat} {ws : List Nat} (valid : kwSortedAfter previous ws = true) :
    (previous :: ws).Pairwise (· < ·) := by
  induction ws generalizing previous with
  | nil => simp
  | cons w tail ih =>
    change (Nat.blt previous w && kwSortedAfter w tail) = true at valid
    obtain ⟨less, sorted⟩ := Bool.and_eq_true_iff.mp valid
    exact List.Pairwise.cons_cons_of_trans (Nat.blt_eq.mp less) (ih sorted)

def kwStateValid (ws : List Nat) : Bool :=
  kwSortedAfter 0 ws && (ws.all fun w => w &&& 16777215 == w)

theorem kwStateValidSpec {ws : List Nat} (valid : kwStateValid ws = true) :
    ws.Nodup ∧ ∀ w ∈ ws, Masked 16777215 w := by
  simp only [kwStateValid, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Masked] at valid
  refine ⟨?_, valid.2⟩
  exact (List.pairwise_cons.mp (kwSortedSpec valid.1)).2.imp (fun h => Nat.ne_of_lt h)

noncomputable def kwAfterCover (maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24)))
    (next memo : (Nat × Nat × (Nat → List Nat))) (fuel : Nat) (ws : List Nat) (hint : Nat) : Bool :=
  ws.length > fuel + 1 ||
    (!ws.contains 4095 && (fuel == 0 || kwReferenceCheck maps next memo ws (some hint) || !kwColor fuel ws))

def kwCoverRest (ws : List Nat) (x y : Nat) : Nat :=
  List.rec 0 (fun w _ next => if w == x || w == y then next else PackedRect.rectW' w ||| next) ws

def kwCoverAdd (rest x y out : Nat) (keep : Nat) : Nat :=
  let left := if keep.testBit 0 then PackedRect.rectW' x else 0
  let right := if keep.testBit 1 then PackedRect.rectW' y else 0
  (rest ||| PackedRect.rectW' out) ||| (left ||| right)

def kwForceWord (word : Nat) (cont : Nat → Bool) : Bool :=
  Nat.rec (cont 0) (fun k _ => cont (k + 1)) word

theorem kwForceWordEq (word : Nat) (cont : Nat → Bool) :
    kwForceWord word cont = cont word := by cases word <;> rfl

def kwForceWords (words : List Nat) (cont : List Nat → Bool) : Bool :=
  (List.rec (motive := fun _ => (List Nat → Bool) → Bool) (fun k => k [])
    (fun w _ next k => kwForceWord w (fun v => next (fun rest => k (v :: rest)))) words) cont

theorem kwForceWordsEq (words : List Nat) (cont : List Nat → Bool) :
    kwForceWords words cont = cont words := by
  induction words generalizing cont with
  | nil => rfl
  | cons w ws ih =>
    change kwForceWord w (fun v => kwForceWords ws (fun rest => cont (v :: rest))) = _
    rw [kwForceWordEq, ih]

def kwRetainedCount (size keep : Nat) : Nat :=
  (size + 1 - (if keep.testBit 0 then 0 else 1)) - (if keep.testBit 1 then 0 else 1)

def kwCachedRest (ws cols : List Nat) (x y : Nat) : Nat :=
  (List.rec (motive := fun _ => List Nat → Nat) (fun _ => 0)
    (fun w _ more cs => List.rec 0 (fun c tail _ =>
      if Nat.beq w x || Nat.beq w y then more tail else Nat.lor c (more tail)) cs) ws) cols

theorem kwCachedRestEq (ws : List Nat) (x y : Nat) :
    kwCachedRest ws (PackedRect.mapW' ws) x y = kwCoverRest ws x y := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change (if Nat.beq w x || Nat.beq w y then kwCachedRest ws (PackedRect.mapW' ws) x y
      else PackedRect.rectW' w ||| kwCachedRest ws (PackedRect.mapW' ws) x y) = _
    rw [ih]
    rfl

def kwCachedAdd (rest x y out : Nat) (keep : Nat) : Nat :=
  (rest ||| out) ||| ((if keep.testBit 0 then x else 0) ||| (if keep.testBit 1 then y else 0))

theorem kwCachedAddEq {ws : List Nat} {a b : Nat} (ha : a < ws.length) (hb : b < ws.length)
    (rest out keep : Nat) :
    kwCachedAdd rest ((PackedRect.mapW' ws).getD a 0) ((PackedRect.mapW' ws).getD b 0)
      (PackedRect.rectW' out) keep = kwCoverAdd rest (ws.getD a 0) (ws.getD b 0) out keep := by
  rw [PackedRect.mapW'_eq]
  simp only [kwCachedAdd, kwCoverAdd, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb, Option.map_some,
    Option.getD_some, PackedRect.rectW'_eq]

def kwScanWords (check : Nat → Nat → Bool) (ws : List Nat) (start : Nat) : Bool :=
  (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ rest i => check i w && rest (i+1)) ws) start

theorem kwScanAt {check : Nat → Nat → Bool} {ws : List Nat} {start i : Nat}
    (ok : kwScanWords check ws start = true) (inside : i < ws.length) :
    check (start+i) (ws.getD i 0) = true := by
  induction ws generalizing start i with
  | nil => simp at inside
  | cons w ws ih =>
    obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
    cases i with
    | zero => exact head
    | succ i =>
      have e : start+i.succ = (start+1)+i := by omega
      rw [e]
      exact ih tail (by simpa using inside)

def kwScanPairs (check : Nat → Nat → Nat → Nat → Bool) (ws : List Nat) (start : Nat) : Bool :=
  (List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w tail rest i => kwScanWords (check i w) tail (i+1) && rest (i+1)) ws) start

theorem kwScanPairAt {check : Nat → Nat → Nat → Nat → Bool} {ws : List Nat} {start a b : Nat}
    (ok : kwScanPairs check ws start = true) (lt : a < b) (inside : b < ws.length) :
    check (start+a) (ws.getD a 0) (start+b) (ws.getD b 0) = true := by
  induction ws generalizing start a b with
  | nil => simp at inside
  | cons w ws ih =>
    obtain ⟨head,tail⟩ := Bool.and_eq_true_iff.mp ok
    cases b with
    | zero => omega
    | succ b =>
      have eb : start+b.succ = (start+1)+b := by omega
      rw [eb]
      cases a with
      | zero => exact kwScanAt head (by simpa using inside)
      | succ a =>
        have ea : start+a.succ = (start+1)+a := by omega
        rw [ea]
        exact ih tail (by omega) (by simpa using inside)

noncomputable def kwCheckState (dom : Bool) (stock : List Nat) (maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24)))
    (next memo : (Nat × Nat × (Nat → List Nat))) (fuel : Nat) (ws : List Nat) (hints : Nat → Nat) : Bool :=
  let n := ws.length
  kwStateValid ws && (n ≤ 64) && !ws.contains 4095 &&
    kwForceWords (PackedRect.mapW' ws) (fun columns =>
      kwScanPairs (fun a x b y =>
          kwForceWord (kwCachedRest ws columns x y) (fun rest =>
            treeBlock 0 2 (fun op =>
              let z := if op == 0 then x &&& y else x ||| y
              (z == 0 || z == 16777215 || stock.contains z || ws.contains z) ||
                kwForceWord (PackedRect.rectW' z) (fun out =>
                  treeBlock 0 4 (fun keep =>
                    (kwRetainedCount n keep > (fuel-1)+1) ||
                    !PackedRect.covR (kwCachedAdd rest (columns.getD a 0) (columns.getD b 0) out keep) ||
                    kwForceWords (kwMove fuel ws x y z keep).2.1
                      (fun child => kwAfterCover maps next memo (fuel-1) child (hints (gateToken a b op keep)))))))) ws 0)

noncomputable def kwFastStateTerm :
    {f : Bool → List Nat → List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24)) → (Nat × Nat × (Nat → List Nat)) → (Nat × Nat × (Nat → List Nat)) →
      Nat → List Nat → (Nat → Nat) → Bool // f = kwCheckState} := by
  refine ⟨?algorithm, ?proof⟩
  case proof =>
    delta kwCheckState treeBlock kwScanPairs kwScanWords kwCachedRest kwCachedAdd PackedRect.mapW' PackedRect.rectW' PackedRect.rectRowMask PackedRect.rectRepeat kwAfterCover kwReferenceCheck kwHintLookup
      kwMove keepWord insertWord kwWordsEq imageWords mixMove mixStep kwForceWords kwForceWord kwColor kwLookup kwTableSize packKW unpackKW
    beta_reduce
    exact rfl

noncomputable def kwFastState := kwFastStateTerm.1

theorem kwFastStateEq : kwFastState = kwCheckState := kwFastStateTerm.2

noncomputable def kwCheckNodeIn (dom : Bool) (stock : List Nat) (maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24)))
    (here next memo : (Nat × Nat × (Nat → List Nat))) (hints : Nat → Nat → Nat) (fuel i : Nat) : Bool :=
  match kwLookup here i with
  | none => false
  | some ws => kwForceWords ws (fun known => kwFastState dom stock maps next memo fuel known (hints i))

noncomputable def kwCheckNode (dom : Bool) (stock : List Nat) (maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24)))
    (levels memo : (Nat → (Nat × Nat × (Nat → List Nat)))) (hints : (Nat → Nat → Nat → Nat)) (fuel i : Nat) : Bool :=
  kwCheckNodeIn dom stock maps (levels fuel) (levels (fuel-1)) (memo (fuel-1)) (hints fuel) fuel i

noncomputable def kwCheckRoots (stock : List Nat) (maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24)))
    (entries memo : (Nat × Nat × (Nat → List Nat))) (fuel : Nat) : Bool :=
  treeBlock 0 (2 ^ stock.length) fun token =>
    kwClosed maps entries memo (rootState stock fuel token)

theorem kwLocal {stock ws : List Nat} {k fuel : Nat}
    (nd : ws.Nodup) (cap : k ≤ fuel)
    (plan : MonoPlan false 16777215 4095 stock k ws.toFinset) :
    ¬ ws.length > fuel + 1 ∧ PackedRect.covR (PackedRect.orFast ws) = true ∧ kwColor fuel ws = true := by
  obtain ⟨cover, coloring⟩ := packedValidClass nd cap plan
  have card := (liveWordSize (monoPlanLive plan)).2
  rw [List.toFinset_card_of_nodup nd] at card
  exact ⟨by omega, by simpa only [PackedRect.orFastEq] using cover,
    by simpa only [kwColor, PackedRect.fastRectEq, PackedRect.packedClassEq] using coloring⟩

noncomputable def kwCheckMemoIn (table : (Nat × Nat × (Nat → List Nat))) (fuel i : Nat) : Bool :=
  match kwLookup table i with
  | none => false
  | some ws => kwForceWords ws (fun known => kwStateValid known && kwPruned fuel known)

noncomputable def kwCheckMemo (memo : (Nat → (Nat × Nat × (Nat → List Nat)))) (fuel i : Nat) : Bool :=
  kwCheckMemoIn (memo fuel) fuel i

theorem kwMemoSound {stock : List Nat} {memo : (Nat → (Nat × Nat × (Nat → List Nat)))} {fuel : Nat}
    (certified : treeBlock 0 (kwTableSize (memo fuel)) (kwCheckMemo memo fuel) = true) :
    ∀ (i : Nat) (ws : List Nat), kwLookup (memo fuel) i = some ws → ∀ k ≤ fuel,
      ¬ MonoPlan false 16777215 4095 stock k ws.toFinset := by
  intro i ws hm k cap plan
  have inside := kwLookupInside hm
  have checked := treeBlock_at certified (Nat.zero_le i) (by simpa using inside)
  simp only [kwCheckMemo, kwCheckMemoIn, hm, kwForceWordsEq, Bool.and_eq_true] at checked
  have ⟨card, cover, color⟩ := kwLocal (kwStateValidSpec checked.1).1 cap plan
  simp [kwPruned, card, cover, color] at checked

theorem kwClosedSound {stock : List Nat} {maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24))}
    (autos : ∀ f ∈ maps, KWAuto 4095 stock f)
    (stockMasked : ∀ w ∈ stock, Masked 16777215 w)
    {entries memo : (Nat × Nat × (Nat → List Nat))} {state : (Nat × List Nat × List (Nat × Nat × Nat))} {hint : Option Nat}
    (refutes : ∀ (i : Nat) (ws : List Nat), kwLookup entries i = some ws → ∀ k ≤ state.1,
      ¬ MonoPlan false 16777215 4095 stock k ws.toFinset)
    (refuteMemo : ∀ (i : Nat) (ws : List Nat), kwLookup memo i = some ws → ∀ k ≤ state.1,
      ¬ MonoPlan false 16777215 4095 stock k ws.toFinset)
    (closed : kwClosed maps entries memo state hint = true)
    (viable : MonoViable false 16777215 4095 stock state) : False := by
  obtain ⟨fuel,ws,history⟩ := state
  obtain ⟨nd, masked, k, cap, plan⟩ := viable
  change k ≤ fuel at cap
  obtain ⟨card, cover, color⟩ := kwLocal nd cap plan
  simp only [kwClosed, card, decide_false, cover, color, Bool.not_true, Bool.false_or,
    Bool.or_false, Bool.and_eq_true] at closed
  rcases Bool.or_eq_true_iff.mp closed.2 with hz | refs
  · have h0 : k = 0 := by rw [beq_iff_eq] at hz; omega
    subst k
    have mem : 4095 ∈ ws.toFinset := by rw [plan.1]; simp
    have absent : 4095 ∉ ws := by simpa using closed.1
    exact absent (List.mem_toFinset.mp mem)
  · obtain ⟨key,i,lookup,equiv⟩ := kwReferenceSpec refs
    have possible : MonoPlan false 16777215 4095 stock k key.toFinset := by
      rcases equiv with rfl | ⟨f,hf,rfl⟩
      · exact plan
      · rw [imageWordsSet f ws (fun w hw => (autos f hf).2 w (masked w hw))]
        exact monoImage (autos f hf).1 stockMasked (fun w hw => masked w (List.mem_toFinset.mp hw)) plan
    rcases lookup with hi | hi
    · exact refutes i key hi k cap possible
    · exact refuteMemo i key hi k cap possible

theorem kwUnionBit (ws : List Nat) (i : Nat) :
    (PackedRect.orFast ws).testBit i = true ↔ ∃ w ∈ ws, (PackedRect.rectW' w).testBit i = true := by
  induction ws with
  | nil => simp [PackedRect.orFast]
  | cons w ws ih =>
    change (PackedRect.rectW' w ||| PackedRect.orFast ws).testBit i = true ↔ _
    simp only [Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨v,hv,ht⟩)
      · exact ⟨w, Or.inl rfl, h⟩
      · exact ⟨v, Or.inr hv, ht⟩
    · rintro ⟨v,rfl | hv, ht⟩
      · exact Or.inl ht
      · exact Or.inr ⟨v,hv,ht⟩

theorem kwRestBit (ws : List Nat) (x y : Nat) (i : Nat) :
    (kwCoverRest ws x y).testBit i = true ↔
      ∃ w ∈ ws, w ≠ x ∧ w ≠ y ∧ (PackedRect.rectW' w).testBit i = true := by
  induction ws with
  | nil => simp [kwCoverRest]
  | cons w ws ih =>
    change (if w == x || w == y then kwCoverRest ws x y
        else PackedRect.rectW' w ||| kwCoverRest ws x y).testBit i = true ↔ _
    by_cases hx : w = x <;> by_cases hy : w = y <;>
      simp only [hx, hy, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true, or_true, true_or,
        or_false, false_or, ↓reduceIte, Nat.testBit_or, ih, List.mem_cons]
    all_goals grind

theorem kwCoverChild {ws : List Nat} {x y w : Nat} {keep fuel : Nat}
    (nd : ws.Nodup) (xy : x ≠ y) (hx : x ∈ ws) (hy : y ∈ ws) :
    kwCoverAdd (kwCoverRest ws x y) x y w keep =
      PackedRect.orFast (kwMove fuel ws x y w keep).2.1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  unfold kwMove
  simp only [kwCoverAdd, kwUnionBit, insertWordMem, Bool.or_eq_true, Nat.testBit_or, kwRestBit]
  cases left : keep.testBit 0 <;> cases right : keep.testBit 1 <;>
    simp only [left, right, keepWord, Bool.false_eq_true, ite_true, ite_false, Nat.zero_testBit,
      or_false, false_or, nd.mem_erase_iff, (nd.erase x).mem_erase_iff] <;> grind

theorem insertWordLength (w : Nat) (ws : List Nat) :
    (insertWord w ws).length = ws.length + 1 := by
  induction ws with
  | nil => rfl
  | cons x xs ih =>
    change (if w ≤ x then w :: x :: xs else x :: insertWord w xs).length = _
    split <;> simp [ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem kwChildLength {ws : List Nat} {x y w : Nat} {keep fuel : Nat}
    (xy : x ≠ y) (hx : x ∈ ws) (hy : y ∈ ws) :
    kwRetainedCount ws.length keep = (kwMove fuel ws x y w keep).2.1.length := by
  have hy' : y ∈ ws.erase x := (List.mem_erase_of_ne xy.symm).mpr hy
  have lb : 0 < (ws.erase x).length := List.length_pos_of_mem hy'
  rw [List.length_erase_of_mem hx] at lb
  change (ws.length + 1 - (if keep.testBit 0 then 0 else 1)) -
    (if keep.testBit 1 then 0 else 1) =
      (insertWord w (keepWord (keep.testBit 1) y (keepWord (keep.testBit 0) x ws))).length
  simp only [insertWordLength]
  cases left : keep.testBit 0 <;> cases right : keep.testBit 1 <;>
    simp only [left, right, Bool.false_eq_true, ite_true, ite_false, keepWord,
      List.length_erase_of_mem hx, List.length_erase_of_mem hy, List.length_erase_of_mem hy',
      Nat.sub_zero] <;> omega

theorem kwChildFrontier {stock : List Nat} {maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24))}
    {next memo : (Nat × Nat × (Nat → List Nat))} {hints : Nat → Nat} {fuel a b op keep : Nat} {ws : List Nat} {child : (Nat × List Nat × List (Nat × Nat × Nat))}
    (checked : kwCheckState false stock maps next memo fuel ws hints = true)
    (ab : a < b) (hb : b < ws.length) (hop : op < 2) (hk : keep < 4)
    (out : Nat) (outEq : out = if op == 0 then ws.getD a 0 &&& ws.getD b 0 else ws.getD a 0 ||| ws.getD b 0)
    (proper : properWord 16777215 out) (fresh : out ∉ ws) (new : out ∉ stock)
    (childFuel : child.1 = fuel - 1)
    (childWords : child.2.1 = (kwMove fuel ws (ws.getD a 0) (ws.getD b 0) out keep).2.1) :
    kwClosed maps next memo child (some (hints (gateToken a b op keep))) = true := by
  simp only [kwCheckState, kwForceWordsEq, Bool.and_eq_true, decide_eq_true_eq] at checked
  have nd := (kwStateValidSpec checked.1.1.1).1
  have pair := kwScanPairAt checked.2 ab hb
  have hv := pair
  simp only [Nat.zero_add] at hv
  rw [kwForceWordEq] at hv
  have opv := treeBlock_at hv (i := op) (Nat.zero_le _) (by omega)
  let x := ws.getD a 0
  let y := ws.getD b 0
  have hx : x ∈ ws := by
    simpa [x, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show a < ws.length by omega)]
      using List.getElem_mem (l := ws) (show a < ws.length by omega)
  have hy : y ∈ ws := by
    simpa [y, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb] using List.getElem_mem (l := ws) hb
  have xy : x ≠ y := by
    intro e
    simp [x,y,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hb,List.getElem?_eq_getElem (show a < ws.length by omega)] at e
    exact (Nat.ne_of_lt ab) (nd.getElem_inj_iff.mp e)
  rw [← outEq, kwForceWordEq] at opv
  have ok := treeBlock_at (by
    simpa [proper.1, proper.2, fresh, new] using opv) (i := keep) (Nat.zero_le _) (by simpa using hk)
  have addEq (rest w keep : Nat) := kwCachedAddEq (Nat.lt_trans ab hb) hb rest w keep
  simp only [List.getD_eq_getElem?_getD] at addEq
  rw [kwCachedRestEq, addEq] at ok
  change (decide (kwRetainedCount ws.length keep > (fuel-1)+1) ||
    !PackedRect.covR (kwCoverAdd (kwCoverRest ws x y) x y out keep) ||
    kwAfterCover maps next memo (fuel-1) (kwMove fuel ws x y out keep).2.1
      (hints (gateToken a b op keep))) = true at ok
  rw [kwChildLength (w := out) (fuel := fuel) xy hx hy,
    kwCoverChild (fuel := fuel) nd xy hx hy, ← childWords] at ok
  rcases Bool.or_eq_true_iff.mp ok with quick | rest
  · rcases Bool.or_eq_true_iff.mp quick with card | cut
    · rcases child with ⟨f,words,history⟩
      have cap : f = fuel - 1 := childFuel
      subst f
      unfold kwClosed
      exact Bool.or_eq_true_iff.mpr (Or.inl (Bool.or_eq_true_iff.mpr (Or.inl card)))
    · rcases child with ⟨f,words,history⟩
      simp [kwClosed, cut]
  · rcases child with ⟨f,words,history⟩
    change f = fuel - 1 at childFuel
    change words = _ at childWords
    change kwAfterCover maps next memo (fuel-1) words (hints (gateToken a b op keep)) = true at rest
    unfold kwAfterCover at rest
    rcases Bool.or_eq_true_iff.mp rest with tooMany | closed
    · simp [kwClosed, childFuel, tooMany]
    · unfold kwClosed
      rw [childFuel]
      exact Bool.or_eq_true_iff.mpr (Or.inr closed)


theorem kwLevelSound {stock : List Nat} {maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24))}
    {levels memo : (Nat → (Nat × Nat × (Nat → List Nat)))} {hints : (Nat → Nat → Nat → Nat)} {budget : Nat}
    (autos : ∀ f ∈ maps, KWAuto 4095 stock f)
    (stockMasked : ∀ w ∈ stock, Masked 16777215 w)
    (certified : ∀ fuel ≤ budget, treeBlock 0 (kwTableSize (levels fuel))
      (kwCheckNode false stock maps levels memo hints fuel) = true)
    (certMemo : ∀ fuel ≤ budget, treeBlock 0 (kwTableSize (memo fuel)) (kwCheckMemo memo fuel) = true) :
    ∀ fuel ≤ budget, ∀ (i : Nat) (ws : List Nat), kwLookup (levels fuel) i = some ws →
      ∀ k ≤ fuel, ¬ MonoPlan false 16777215 4095 stock k ws.toFinset := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | ind fuel ih =>
    intro bf i ws fromLevel k cap plan
    have inside := kwLookupInside fromLevel
    have checked := treeBlock_at (certified fuel bf) (Nat.zero_le i) (by simpa using inside)
    have ok : kwCheckState false stock maps (levels (fuel-1)) (memo (fuel-1)) fuel ws (hints fuel i) = true := by
      simpa only [kwCheckNode, kwCheckNodeIn, kwFastStateEq, kwForceWordsEq, fromLevel] using checked
    have components := ok
    simp only [kwCheckState, Bool.and_eq_true, decide_eq_true_eq] at components
    obtain ⟨nd, masked⟩ := kwStateValidSpec components.1.1.1
    have width := components.1.1.2
    have absent : 4095 ∉ ws := by simpa using components.1.2
    have v : MonoViable false 16777215 4095 stock (fuel, ws, []) := ⟨nd,masked,k,cap,plan⟩
    have fuelPos : 0 < fuel := by
      by_contra! empty
      have kz : k = 0 := by omega
      subst k
      exact absent (List.mem_toFinset.mp (by rw [plan.1]; simp))
    rcases monoProgress width v with hit | ⟨a,b,op,keep,child,ab,hb,hop,hk,eval,allow,hproper,hfresh,hnew,childWords,childFuel,childOK⟩
    · exact absent hit
    have childClosed := kwChildFrontier ok ab hb hop hk _ rfl hproper hfresh hnew childFuel childWords
    apply kwClosedSound autos stockMasked _ _ childClosed childOK
    · intro j ys found k' bound
      change child.1 = fuel - 1 at childFuel
      rw [childFuel] at bound
      exact ih (fuel-1) (by omega) (by omega) j ys found k' bound
    · intro j ys found k' bound
      change child.1 = fuel - 1 at childFuel
      rw [childFuel] at bound
      exact kwMemoSound (certMemo (fuel-1) (by omega)) j ys found k' bound

theorem lowerKW {roots stock : List Nat} {maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24))} {levels memo : (Nat → (Nat × Nat × (Nat → List Nat)))} {hints : (Nat → Nat → Nat → Nat)}
    {budget : Nat}
    (autos : ∀ f ∈ maps, KWAuto 4095 stock f)
    (stockMasked : ∀ w ∈ stock, Masked 16777215 w)
    (rootMasked : ∀ w ∈ roots, Masked 16777215 w)
    (stockNd : stock.Nodup) (stockSub : ∀ w ∈ stock, w ∈ roots)
    (cover : ∀ w ∈ roots, properWord 16777215 w → w ∈ stock)
    (rootCheck : kwCheckRoots stock maps (levels budget) (memo budget) budget = true)
    (certified : ∀ fuel ≤ budget, treeBlock 0 (kwTableSize (levels fuel))
      (kwCheckNode false stock maps levels memo hints fuel) = true)
    (certMemo : ∀ fuel ≤ budget, treeBlock 0 (kwTableSize (memo fuel)) (kwCheckMemo memo fuel) = true) :
    MonoLower 16777215 roots 4095 (budget + 1) := by
  intro values build hit
  by_contra! short
  obtain ⟨k,S,hk,plan,sub⟩ := extractMonoPlan stockSub rootMasked (monoAdmissible build) hit
    (by unfold properWord; decide : properWord 16777215 4095)
  have stockCovers : S ⊆ stock.toFinset := by
    intro w hw
    exact List.mem_toFinset.mpr (cover w (sub w hw) (liveWordProper (monoPlanLive plan) w hw))
  obtain ⟨token, ht, eq⟩ := rootToken stock S
  rw [Finset.inter_eq_right.mpr stockCovers] at eq
  have ok := treeBlock_at rootCheck (Nat.zero_le token) (by simpa using ht)
  apply kwClosedSound (state := rootState stock budget token) (memo := memo budget) autos stockMasked
    (kwLevelSound autos stockMasked certified certMemo budget (Nat.le_refl _))
    (kwMemoSound (certMemo budget (Nat.le_refl _))) ok
  have sublist := rootWordSublist stock token
  refine ⟨sublist.nodup stockNd, fun w hw => stockMasked w (sublist.subset hw), k, ?_, ?_⟩
  · change k ≤ budget
    omega
  · change MonoPlan false 16777215 4095 stock k (rootWords stock token).toFinset
    rwa [eq]

theorem monoBuildsWeaken {mask : Nat} {small big values : List Nat}
    (supply : ∀ w ∈ small, AvailableWord mask big w) (build : MonoBuilds mask small values) :
    MonoBuilds mask big values := by
  induction values generalizing small big with
  | nil => trivial
  | cons v vs ih =>
    obtain ⟨a,b,ha,hb,g⟩ := build.1
    refine ⟨⟨a,b,availableWeaken supply ha,availableWeaken supply hb,g⟩, ih ?_ build.2⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inr (Or.inr List.mem_cons_self)
    · exact availableWeaken (fun x hx => Or.inr (Or.inr (List.mem_cons_of_mem _ hx))) (supply _ hw)

theorem monoBuildsIndex {mask : Nat} (bank values : List Nat)
    (legal : ∀ i, i < values.length →
      MonoGate mask (bank ++ values.take i) (values.getD i 0)) :
    MonoBuilds mask bank values := by
  induction values generalizing bank with
  | nil => trivial
  | cons v vs ih =>
    have first := legal 0 (by simp)
    have tail : ∀ i, i < vs.length →
        MonoGate mask ((bank ++ [v]) ++ vs.take i) (vs.getD i 0) := by
      intro i hi
      simpa [List.take_succ_cons, List.append_assoc] using legal (i + 1) (by simpa using hi)
    refine ⟨by simpa using first, monoBuildsWeaken ?_ (ih (bank ++ [v]) tail)⟩
    intro w mem
    exact Or.inr (Or.inr (by simpa [or_comm] using mem))

theorem monoPrefixLower (values : List (BitVec rows)) (baseCount : Nat)
    (goal : BitVec rows) (minimum : Nat)
    (h : MonoLower (fullMask rows) ((values.take baseCount).map BitVec.toNat) goal.toNat minimum)
    (cap : values.length - baseCount < minimum)
    (legal : ∀ i, baseCount ≤ i → i < values.length →
      MonoGate (fullMask rows) ((values.take i).map BitVec.toNat) (values.getD i 0).toNat) :
    goal ∉ values := by
  intro hit
  let bank := (values.take baseCount).map BitVec.toNat
  let vals := (values.drop baseCount).map BitVec.toNat
  have builds : MonoBuilds (fullMask rows) bank vals := by
    apply monoBuildsIndex
    intro i hi
    have hb : baseCount + i < values.length := by
      have hi' : i < values.length - baseCount := by simpa [vals] using hi
      omega
    have step := legal (baseCount + i) (Nat.le_add_right ..) hb
    have pool : bank ++ vals.take i = (values.take (baseCount + i)).map BitVec.toNat := by
      simp only [bank, vals, ← List.map_take, ← List.map_append]
      rw [List.take_add]
    have value : vals.getD i 0 = (values.getD (baseCount + i) 0).toNat := by
      have eq := List.getD_map (l := values.drop baseCount) (f := BitVec.toNat) (n := i) (d := (0 : BitVec rows))
      simpa [vals, List.getD_eq_getElem?_getD, List.getElem?_drop] using eq
    rw [pool, value]
    exact step
  apply Nat.not_le_of_lt cap
  have av : AvailableWord (fullMask rows) (vals ++ bank) goal.toNat := by
    have hm : goal.toNat ∈ bank ++ vals := by
      have all : bank ++ vals = values.map BitVec.toNat := by simp [bank, vals, ← List.map_append]
      rw [all]
      exact List.mem_map_of_mem hit
    exact Or.inr (Or.inr (by simpa [List.mem_append, or_comm] using hm))
  simpa [vals] using h vals builds av

theorem monoIndexedConst {bank : List (BitVec rows)} {w : BitVec rows}
    (eq : w = BitVec.allOnes rows) :
    MonoGate (fullMask rows) (bank.map BitVec.toNat) w.toNat := by
  exact ⟨fullMask rows, 0, Or.inr (Or.inl rfl), Or.inl rfl, Or.inr (by simp [eq, fullMask])⟩

theorem monoIndexedPair {bank : List (BitVec rows)} {w a b : BitVec rows}
    (ha : a ∈ bank) (hb : b ∈ bank) (gate : w = a &&& b ∨ w = a ||| b) :
    MonoGate (fullMask rows) (bank.map BitVec.toNat) w.toNat := by
  refine ⟨a.toNat, b.toNat, Or.inr (Or.inr (List.mem_map_of_mem ha)),
    Or.inr (Or.inr (List.mem_map_of_mem hb)), ?_⟩
  rcases gate with rfl | rfl
  · exact Or.inl (BitVec.toNat_and ..)
  · exact Or.inr (BitVec.toNat_or ..)

def repGateVal {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    BitVec rows :=
  let args := g.inputs.map fun i => bank.getD i 0
  match g.op with
  | PEqualNP.CircuitLowerBounds.GateOp.and => args.foldr (· &&& ·) (BitVec.allOnes rows)
  | PEqualNP.CircuitLowerBounds.GateOp.or => args.foldr (· ||| ·) 0
  | _ => 0

def repStep {rows : Nat} (bank : List (BitVec rows)) (g : PEqualNP.CircuitLowerBounds.Gate) :
    List (BitVec rows) :=
  bank ++ [repGateVal bank g]

theorem repGetDBit {rows : Nat} (bank : List (BitVec rows)) (i k : Nat) :
    (bank.getD k 0).getLsbD i = (bank.map fun w => w.getLsbD i).getD k false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases bank[k]? <;> simp

theorem repAndBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· &&& ·) (BitVec.allOnes rows)).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).all id := by
  induction xs with
  | nil => simp [i.isLt]
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_and, List.map_cons, List.all_cons, id_eq, ih]

theorem repOrBit {rows : Nat} (xs : List (BitVec rows)) (i : Fin rows) :
    (xs.foldr (· ||| ·) 0).getLsbD i.val = (xs.map fun w => w.getLsbD i.val).any id := by
  induction xs with
  | nil => simp
  | cons a t ih => simp only [List.foldr_cons, BitVec.getLsbD_or, List.map_cons, List.any_cons, id_eq, ih]

theorem repGateBit {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp)) :
    (repGateVal bank g).getLsbD i.val =
      g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with rfl | rfl
  · simp only [repGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, repAndBit, List.map_map]
    congr 1; apply List.map_congr_left; intro k _; exact repGetDBit bank i.val k
  · simp only [repGateVal, PEqualNP.CircuitLowerBounds.GateOp.eval, repOrBit, List.map_map]
    congr 1; apply List.map_congr_left; intro k _; exact repGetDBit bank i.val k

theorem repFoldBits {rows : Nat} (bank : List (BitVec rows)) (i : Fin rows)
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hmon : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    (gs.foldl repStep bank).map (fun w => w.getLsbD i.val) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)])
        (bank.map fun w => w.getLsbD i.val) := by
  induction gs generalizing bank with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hstep : (repStep bank g).map (fun w => w.getLsbD i.val) =
        (bank.map fun w => w.getLsbD i.val) ++
          [g.op.eval (g.inputs.map fun k => (bank.map fun w => w.getLsbD i.val).getD k false)] := by
      simp only [repStep, List.map_append, List.map_cons, List.map_nil,
        repGateBit bank i g (hmon g List.mem_cons_self).1]
    rw [ih (repStep bank g) (fun g' hg' => hmon g' (List.mem_cons_of_mem _ hg')), hstep]

theorem repMonoOfAv {mask : Nat} {bank : List Nat} {w : Nat}
    (av : AvailableWord mask bank w) : MonoGate mask bank w :=
  ⟨w, 0, av, Or.inl rfl, Or.inr (by simp)⟩

theorem repGateMono {rows : Nat} (bank : List (BitVec rows))
    (g : PEqualNP.CircuitLowerBounds.Gate)
    (hop : g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp))
    (hlen : g.inputs.length ≤ 2) :
    MonoGate (fullMask rows) (bank.map BitVec.toNat) (repGateVal bank g).toNat := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  have zeroAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) 0 := Or.inl rfl
  have maskAv : AvailableWord (fullMask rows) (bank.map BitVec.toNat) (fullMask rows) :=
    Or.inr (Or.inl rfl)
  rcases hop with rfl | rfl
  · cases ins with
    | nil => exact repMonoOfAv (by simpa [repGateVal, fullMask] using maskAv)
    | cons a t =>
      cases t with
      | nil => exact repMonoOfAv (by simpa [repGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inl (by simp [repGateVal, BitVec.toNat_and])⟩
        | cons c t => simp at hlen
  · cases ins with
    | nil => exact repMonoOfAv (by simpa [repGateVal] using zeroAv)
    | cons a t =>
      cases t with
      | nil => exact repMonoOfAv (by simpa [repGateVal] using toNatAvailable bank a)
      | cons b t =>
        cases t with
        | nil =>
          exact ⟨_, _, toNatAvailable bank a, toNatAvailable bank b,
            Or.inr (by simp [repGateVal, BitVec.toNat_or])⟩
        | cons c t => simp at hlen

theorem repMonoBuilds {rows : Nat} (bank : List (BitVec rows))
    (gs : List PEqualNP.CircuitLowerBounds.Gate)
    (hmon : ∀ g ∈ gs, g.op ∈ ({PEqualNP.CircuitLowerBounds.GateOp.and,
      PEqualNP.CircuitLowerBounds.GateOp.or} : Set PEqualNP.CircuitLowerBounds.GateOp) ∧
      g.inputs.length ≤ 2) :
    ∃ vs, vs.length = gs.length ∧ MonoBuilds (fullMask rows) (bank.map BitVec.toNat) vs ∧
      ∀ v ∈ gs.foldl repStep bank, v.toNat ∈ vs ++ bank.map BitVec.toNat := by
  induction gs generalizing bank with
  | nil => exact ⟨[], rfl, trivial, fun _ h => List.mem_map_of_mem h⟩
  | cons g gs ih =>
    let v := repGateVal bank g
    have hg := hmon g List.mem_cons_self
    obtain ⟨xs, len, build, sub⟩ := ih (repStep bank g) (fun g' hg' => hmon g' (List.mem_cons_of_mem _ hg'))
    have eq : (repStep bank g).map BitVec.toNat = bank.map BitVec.toNat ++ [v.toNat] := by
      simp [repStep, v]
    rw [eq] at build
    refine ⟨v.toNat :: xs, by simp [len], ⟨repGateMono bank g hg.1 hg.2, monoBuildsWeaken ?_ build⟩, ?_⟩
    · intro u hu; exact Or.inr (Or.inr (by simpa [or_comm] using hu))
    · intro u hu; have m := sub u hu; rw [eq] at m
      simpa [List.mem_append, or_assoc, or_left_comm, or_comm] using m

theorem repLowerOnRows {n m q : Nat} (rows : Fin q → Fin n × Fin m)
    (raw : List (BitVec q)) (goal : BitVec q) (minimum : Nat)
    (A : Fin n → Fin m → Bool)
    (inputs : ∀ i : Fin q, raw.map (fun w => w.getLsbD i.val) =
      PEqualNP.Represents.oneEach (rows i).1 (rows i).2)
    (output : ∀ i : Fin q, goal.getLsbD i.val = A (rows i).1 (rows i).2)
    (lower : MonoLower (fullMask q) (raw.map BitVec.toNat) goal.toNat minimum)
    (k : Nat) (h : PEqualNP.Represents.RepSizeAtMost A k) : minimum ≤ k := by
  obtain ⟨C, monotone, size, represents⟩ := h
  obtain ⟨values, length, builds, subset⟩ := repMonoBuilds raw C.gates monotone
  let bank := C.gates.foldl repStep raw
  have equal : bank.getD C.output 0 = goal := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let i : Fin q := ⟨j, hj⟩
    have hbits := repFoldBits raw i C.gates monotone
    have eval : (C.wires (PEqualNP.Represents.oneEach (rows i).1 (rows i).2)).getD C.output false =
        A (rows i).1 (rows i).2 := represents _ _
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun l => w.getD l false)])
      (PEqualNP.Represents.oneEach (rows i).1 (rows i).2)).getD C.output false = _ at eval
    rw [← inputs i, ← hbits] at eval
    change (bank.getD C.output 0).getLsbD i.val = goal.getLsbD i.val
    rw [output i, ← eval, ← repGetDBit]
  have available : AvailableWord (fullMask q) (values ++ raw.map BitVec.toNat) goal.toNat := by
    rw [← equal, List.getD_eq_getElem?_getD]
    cases member : bank[C.output]? with
    | none => exact Or.inl rfl
    | some w => exact Or.inr (Or.inr (subset w (List.mem_of_getElem? member)))
  have bound := lower values builds available
  have gateCount : C.gates.length ≤ k := size
  omega

def c0b0Stock : List Nat := [266695, 534625, 1599000, 2130570, 4527120, 9584900, 14911520]

def c0b0Map0Rows (i : Fin 24) : Fin 24 := ([6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5, 18, 19, 20, 21, 22, 23, 12, 13, 14, 15, 16, 17] : List (Fin 24)).getD i.val 0

def c0b0Map0 : ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24)) := ([([(0x3f03f, 6)], [(0xfc0fc0, 6)])], c0b0Map0Rows)

def c0b0Maps : List ((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 24 → Fin 24)) := [c0b0Map0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c0b0Autos : ∀ f ∈ c0b0Maps, KWAuto 4095 c0b0Stock f := by
  simp only [c0b0Maps, List.mem_cons, List.not_mem_nil, or_false]
  intro f h
  rcases h with rfl
  · change MonoAuto 4095 c0b0Stock c0b0Map0Rows ∧ _
    refine ⟨by unfold MonoAuto Function.Surjective; decide +kernel, ?_⟩
    intro w h
    exact wordMoveAgreement (by unfold Masked; decide +kernel) (by decide +kernel) h

def c0b0Dictionary : Nat := 0x0

def c0b0Levels : (Nat → (Nat × Nat × (Nat → List Nat)))
  | _ => (0, 0, fun _ => [])

def c0b0Memo : (Nat → (Nat × Nat × (Nat → List Nat)))
  | _ => (0, 0, fun _ => [])

def c0b0Hints : (Nat → Nat → Nat → Nat)
  | _, _, _ => 0

noncomputable def c0b0RootCheck (token : Nat) := kwClosed c0b0Maps (c0b0Levels 7) (c0b0Memo 7) (rootState c0b0Stock 7 token)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c0b0RootsBlock0 : treeBlock 0 64 c0b0RootCheck = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem c0b0RootsBlock64 : treeBlock 64 64 c0b0RootCheck = true := by
  decide +kernel

theorem c0b0RootsVerified : treeBlock 0 128 c0b0RootCheck = true :=
  (@treeBlock_merge 0 64 64 c0b0RootCheck c0b0RootsBlock0 c0b0RootsBlock64)

theorem c0b0Roots : kwCheckRoots c0b0Stock c0b0Maps (c0b0Levels 7) (c0b0Memo 7) 7 = true := c0b0RootsVerified

theorem c0b0Certified : ∀ fuel ≤ 7, treeBlock 0 (kwTableSize (c0b0Levels fuel)) (kwCheckNode false c0b0Stock c0b0Maps c0b0Levels c0b0Memo c0b0Hints fuel) = true := by
  intro fuel cap
  interval_cases fuel
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl

theorem c0b0MemoCertified : ∀ fuel ≤ 7, treeBlock 0 (kwTableSize (c0b0Memo fuel)) (kwCheckMemo c0b0Memo fuel) = true := by
  intro fuel cap
  interval_cases fuel
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl

theorem c0b0Lower : MonoLower 16777215 [266695, 1599000, 14911520, 534625, 2130570, 4527120, 9584900] 4095 8 := by

  apply lowerKW c0b0Autos _ _ _ _ _ c0b0Roots c0b0Certified c0b0MemoCertified

  · simp only [c0b0Stock, List.mem_cons, List.not_mem_nil, or_false, Masked]
    intro w h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Masked]
    intro w h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · unfold c0b0Stock
    decide +kernel
  · simp only [c0b0Stock, List.mem_cons, List.not_mem_nil, or_false]
    intro w h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · simp only [List.mem_cons, List.not_mem_nil, or_false, properWord]
    intro w h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

def twinRows (i : Fin 24) : Fin 3 × Fin 4 :=
  ([(0, 0), (0, 1), (0, 3), (1, 1), (1, 2), (2, 0), (0, 0), (0, 1), (0, 3), (1, 1), (1, 2), (2, 0), (0, 2), (1, 0), (1, 3), (2, 1), (2, 2), (2, 3), (0, 2), (1, 0), (1, 3), (2, 1), (2, 2), (2, 3)] : List (Fin 3 × Fin 4)).getD i.val (0, 0)

def twinBase : List (BitVec 24) := [266695, 1599000, 14911520, 534625, 2130570, 4527120, 9584900]

end PEqualNP.Outside.L_meta_25826

open PEqualNP.Outside.L_meta_25826 in
theorem PEqualNP.Outside.L_meta_25826 : ¬ (PEqualNP.Represents.RepSizeAtMost (fun (u : Fin 3) (v : Fin 4) => (363 : ℕ).testBit (4 * u.val + v.val)) 7) := by
  intro existsCircuit
  have lower := repLowerOnRows twinRows twinBase (4095 : BitVec 24) 8 _
    (by decide +kernel) (by decide +kernel) c0b0Lower 7 existsCircuit
  omega

