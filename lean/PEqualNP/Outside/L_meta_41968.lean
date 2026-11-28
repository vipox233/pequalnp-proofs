import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41968

def unpack (packed width index : Nat) : Nat :=
  (packed >>> (width * index)) &&& ((1 <<< width) - 1)

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

theorem pointZero : pointWord (fun _ : Fin rows => false) = 0 := by
  have eq : encodePoint (fun _ : Fin rows => false) = 0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [encodeBit _ ⟨i, hi⟩]
    simp
  simp [pointWord, eq]

theorem relabelZero (sourceIndex : Fin rows → Fin rows) : relabel sourceIndex 0 = 0 := by
  simpa [relabel] using (pointZero (rows := rows))

theorem relabelAnd (sourceIndex : Fin rows → Fin rows) (a b : Nat) :
    relabel sourceIndex (a &&& b) = relabel sourceIndex a &&& relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_and, pointWord, encodeAnd, BitVec.toNat_and]

theorem relabelOr (sourceIndex : Fin rows → Fin rows) (a b : Nat) :
    relabel sourceIndex (a ||| b) = relabel sourceIndex a ||| relabel sourceIndex b := by
  simp only [relabel, Nat.testBit_or, pointWord, encodeOr, BitVec.toNat_or]

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

def full : ℕ := ((1 <<< 144) - 1)

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

def rowM : ℕ := (1 <<< 0) ||| (1 <<< 12) ||| (1 <<< 24) ||| (1 <<< 36) ||| (1 <<< 48) ||| (1 <<< 60) ||| (1 <<< 72) ||| (1 <<< 84) ||| (1 <<< 96) ||| (1 <<< 108) ||| (1 <<< 120) ||| (1 <<< 132)

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
        (if ws.length == fuel + 1 then !dagPartition true ws goal (mask ^^^ goal)
         else !dagPartition false ws goal (mask ^^^ goal)) ||
        (if ws.length == fuel + 1 then
           chart.any (fun c => !PackedRect.rectOK1 (ws.map (chartWord c)))
         else false) || cut state))

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
  List.rec 0 (fun w _ tail => (w &&& fullMask 64) ||| (tail <<< 64)) ws

def dagLaneMarks (n : Nat) : Nat :=
  Nat.rec 0 (fun _ more => 1 ||| (more <<< 64)) n

def dagOmitted (a b : Nat) (left right : Bool) : Nat :=
  (if left then 0 else 1 <<< (64*a)) ||| (if right then 0 else 1 <<< (64*b))

def dagPackedPair (mask goal packed marks erased out : Nat) (directed : Bool) (pairs : List Nat) : Bool :=
  pairs.any fun code =>
    dagForceWord code (fun code =>
      dagForceWord (code &&& 511) (fun p =>
        dagForceWord (code >>> 9) (fun n =>
          let up := (packed >>> p) &&& marks
          let down := (packed >>> n) &&& marks
          let contrast := if directed then up &&& (down ^^^ marks) else up ^^^ down
          let gateOK := if directed then !out.testBit p || out.testBit n else out.testBit p == out.testBit n
          goal.testBit p && mask.testBit n && !goal.testBit n && Nat.blt p 64 && Nat.blt n 64 &&
            gateOK && Nat.beq (contrast &&& (marks ^^^ erased)) 0)))

theorem dagPackBits {ws : List Nat} {i row : Nat} (inside : i < ws.length) (width : row < 64) :
    (dagPackWords ws).testBit (64*i+row) = (ws.getD i 0).testBit row := by
  induction ws generalizing i with
  | nil => simp at inside
  | cons w ws ih =>
    change ((w &&& fullMask 64) ||| (dagPackWords ws <<< 64)).testBit (64*i+row) = _
    have test (n j : Nat) : (fullMask n).testBit j = decide (j < n) := by simp [fullMask, Nat.testBit_two_pow_sub_one]
    rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, test]
    cases i with
    | zero => simp [fullMask, Nat.testBit_two_pow_sub_one, width, Nat.not_le.mpr width]
    | succ i =>
      have hi : i < ws.length := by simpa using inside
      have crossed : 64 ≤ 64*i.succ+row := by omega
      have offset : 64*i.succ+row-64 = 64*i+row := by omega
      have past : ¬ 64*i.succ+row < 64 := by omega
      simp [crossed, offset, fullMask, Nat.testBit_two_pow_sub_one, past, ih hi]

theorem dagMarkBits {length i : Nat} (inside : i < length) :
    (dagLaneMarks length).testBit (64*i) = true := by
  induction length generalizing i with
  | zero => omega
  | succ length ih =>
    change (1 ||| (dagLaneMarks length <<< 64)).testBit (64*i) = true
    rw [Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero => simp
    | succ i =>
      have hi : i < length := by omega
      have crossed : 64 ≤ 64*i.succ := by omega
      have offset : 64*i.succ-64 = 64*i := by omega
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

def dagCheckNode (mask goal : Nat) (chart : Option ({ rows : List Nat // rows.length = 24 })) (cut : Nat → ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool))
    (count : Nat) (states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))) (moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))) (links : (Nat → Nat → Option (Nat × Nat)))
    (sample : (Nat × Nat)) (tags : Nat → List (Nat × Nat)) (i : Nat) : Bool :=
  match states i with
  | none => false
  | some (fuel, ws, history) => dagForceWords ws (fun forced =>
      dagStateOK mask forced && dagCheckChildren mask goal chart (cut i)
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
  have omitted : (dagOmitted a b left right).testBit (64*i) = false := by
    have cleared (j : Nat) (keep : Bool) (h : keep = true ∨ w ≠ ws.getD j 0) :
        (if keep then 0 else 1 <<< (64*j)).testBit (64*i) = false := by
      rcases h with yes | diff
      · simp [yes]
      · have ne : i ≠ j := fun same => diff (same ▸ atIndex).symm
        cases keep <;> simp [Nat.shiftLeft_eq, Nat.testBit_two_pow, show 64*j ≠ 64*i by omega]
    simp [dagOmitted, Nat.testBit_or, cleared a left leftMem.2, cleared b right rightMem.2]
  let p := code &&& 511
  let n := code >>> 9
  let marks := dagLaneMarks ws.length
  let signal := dagPackWords ws
  have mark : marks.testBit (64*i) = true := dagMarkBits inside
  have test {j : Nat} (within : j < 64) :
      ((signal >>> j) &&& marks).testBit (64*i) = w.testBit j := by
    rw [Nat.testBit_and, Nat.testBit_shiftRight, mark, Bool.and_true,
      Nat.add_comm j, dagPackBits inside within, atIndex]
  have h := congrArg (fun word => Nat.testBit word (64*i)) (Nat.beq_eq.mp closure)
  simp only [Nat.zero_testBit] at h
  change (((if directed then (signal >>> p &&& marks) &&& ((signal >>> n &&& marks) ^^^ marks)
      else (signal >>> p &&& marks) ^^^ (signal >>> n &&& marks)) &&&
    (marks ^^^ dagOmitted a b left right)).testBit (64*i)) = false at h
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

theorem dagAllNodes {mask goal : Nat} {width count : Nat}
    {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {cut : Nat → ((Nat × List Nat × List (Nat × Nat × Nat)) → Bool)} {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))} {moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))} {links : (Nat → Nat → Option (Nat × Nat))} {sample : (Nat × Nat)}
    {tags : Nat → List (Nat × Nat)}
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (cutSound : ∀ i s, WordViable mask goal s → cut i s = false)
    (autos : DagMovesOK mask goal width moves)
    (verified : treeBlock 0 count (dagCheckNode mask goal chart cut count
      states moves links sample tags) = true):
    ∀ cap i saved, i < count → states i = some saved →
      saved.1 = cap → ∀ k t, k ≤ cap → ¬LiveWord mask goal k t saved.2.1.toFinset := by
  intro cap
  induction cap using Nat.strong_induction_on with
  | ind cap ih =>
    intro i s iBound stateEq sFuel k t kBound live
    rcases s with ⟨remaining, words, history⟩
    let s : (Nat × List Nat × List (Nat × Nat × Nat)) := (remaining, words, history)
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
    have r := dagChildAt ok ha legal eval goalMask cv nd (dagLocalOpen goalMask chartOK cv (cutSound i _ cv))
    have ⟨less,cm⟩ := childStateData eval masked
    have below : child.1 < cap := sFuel ▸ less
    obtain ⟨_,k',t',fits,clive⟩ := cv
    obtain ⟨j,dest,bound,restore,fuelEq,tail⟩ :=
      dagLinked maskBounds autos cm r clive
    exact ih child.1 below j dest bound restore fuelEq k' t' fits tail

def cutPick {α : Type} : List α → Nat → List α
  | [], _ => []
  | x :: xs, n => if n = 0 then [] else if n.testBit 0 then x :: cutPick xs (n >>> 1) else cutPick xs (n >>> 1)
theorem cutPickMem {α : Type} (l : List α) (n : Nat) : cutPick l n ⊆ l := by
  induction l generalizing n with
  | nil => simp [cutPick]
  | cons x xs ih =>
    unfold cutPick
    split
    · simp
    · split
      · exact List.cons_subset_cons _ (ih _)
      · exact List.Subset.trans (ih _) (List.subset_cons_self ..)

theorem lowerDag {mask goal : Nat} {width fuel count : Nat}
    {stock : List Nat} {chart : Option ({ rows : List Nat // rows.length = 24 })}
    {states : Nat → Option (Nat × List Nat × List (Nat × Nat × Nat))} {moves : Array (List (List (Nat × Nat) × List (Nat × Nat)))} {links : (Nat → Nat → Option (Nat × Nat))} {sample : (Nat × Nat)}
    {tags : Nat → List (Nat × Nat)}
    {bounds : List (Nat × List Nat × Nat × Nat)} {witnesses : List (Nat × Nat × Nat)}
    (choices : Nat → Nat)
    (maskBounds : Masked (fullMask width) mask)
    (goalMask : Masked mask goal) (proper : properWord mask goal)
    (chartOK : ∀ c, chart = some c → ChartOK goal c)
    (autos : DagMovesOK mask goal width moves)
    (stockMasked : ∀ w ∈ stock, Masked mask w) (stockNd : stock.Nodup)
    (essential : witnesses.all (essentialB mask goal stock) = true)
    (known : Known bounds) (submasks : ∀ b ∈ bounds, mask &&& b.1 = b.1)
    (rootCheck : dagCheckRoots mask goal chart (dagKnownCloses goal bounds) witnesses
      (dagRef count states moves links 0)
      stock fuel = true)
    (nodeCheck : treeBlock 0 count (dagCheckNode mask goal chart (fun i => dagKnownCloses goal (cutPick bounds (choices i)))
      count states moves links sample tags) = true) :
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
    dagRef count states moves links 0 token state) = true at checked
  simp only [allowed,openRoot,Bool.not_true,Bool.false_or] at checked
  have slim (i : Nat) (s) (h : WordViable mask goal s) : dagKnownCloses goal (cutPick bounds (choices i)) s = false := by
    rw [dagKnownClosesEq]
    exact knownClosesSound (fun b hb => known b (cutPickMem _ _ hb)) (fun b hb => submasks b (cutPickMem _ _ hb)) h
  have finish := dagAllNodes maskBounds goalMask chartOK slim autos nodeCheck
  have fits : k ≤ fuel := by omega
  have still : LiveWord mask goal k t state.2.1.toFinset := by rwa [eq']
  have stateMask : ∀ w ∈ state.2.1, Masked mask w := by
    intro w hw
    exact stockMasked _ ((rootWordSublist stock token).subset hw)
  obtain ⟨i,s,hi,restore,cap,plan⟩ := dagLinked maskBounds autos stateMask checked still
  exact finish fuel i s hi restore cap k t fits plan

def pageLinks (idx codeAt : Nat → Nat) (sizeBits tokenBits destinationBits trials : Nat) :
    (Nat → Nat → Option (Nat × Nat)) := fun parent token =>
  let entry := idx parent
  let size := entry &&& ((1 <<< sizeBits) - 1)
  let offset := entry >>> sizeBits
  (Nat.rec (motive := fun _ => Nat → Nat → Option (Nat × Nat)) (fun _ _ => none)
    (fun _ next lo hi =>
      if Nat.blt lo hi then
        let mid := (lo+hi)/2
        let code := codeAt mid
        let key := code &&& ((1 <<< tokenBits) - 1)
        if Nat.beq token key then
          some ((code >>> tokenBits) &&& ((1 <<< destinationBits) - 1),
            code >>> (tokenBits + destinationBits))
        else if Nat.blt token key then next lo mid else next (mid+1) hi
      else none) trials) offset (offset+size)

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

def sGoal : Nat := 0xfeeaeaaaeaaac880
def cbits (ws : List Nat) : Nat := ws.foldr (fun a z => (z <<< 64) ||| a) 0
def materialize (raw : List Nat) (shift mask maxCount entry : Nat) : List Nat :=
  let base := rootWords raw (entry &&& 63)
  Nat.rec (motive := fun _ => Nat → List Nat) (fun _ => base)
    (fun _ rest c => if Nat.beq c 0 then base else
      insertWord ((c &&& mask) - 1) (rest (c >>> shift))) maxCount (entry >>> 6)
def shortHist (mask fuel : Nat) (atWords : Nat → List Nat) (forest : Nat → Nat × Nat) (i : Nat) : List (Nat × Nat × Nat) :=
  (Nat.rec (motive := fun _ => Nat → List (Nat × Nat × Nat)) (fun _ => [])
    (fun _ prev j => let (p,token) := forest j
                     if Nat.beq p 0 then [] else
                     let ws := atWords (p-1)
                     let x := ws.getD (token / 768) 0
                     let y := ws.getD ((token / 12) % 64) 0
                     let op := token / 4 % 3
                     (dagGateWord mask op x y, x, y) :: prev (p-1)) (fuel+1)) i
def s0Blob175105 : Nat := (cbits [0x2c060b0301c0607,0xc0407050380c0e05,0xc0f0183c040e0102,0xe0302c14070503c0,0x103c060])
def s0Blob175230 : Nat := 0xefbcdf73becf
def s0Blob175271 : Nat := 0x182824124205
def s0Mask : Nat := 0xcccc
abbrev s0Goal : Nat := sGoal &&& s0Mask
abbrev s0StockWords : List Nat := [0x8888,0xc0c0,0xcc00]
def s0Fact : Nat × List Nat × Nat × Nat := (s0Mask, s0StockWords, 4, s0Goal)
def s0Cuts : List (Nat × List Nat × Nat × Nat) := []
def s0Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 11, 14, 7, 11, 14, 7, 11, 14, 7, 11, 14, 3, 6, 10, 3, 6, 10, 3, 6, 10, 3, 6, 10], rfl⟩
def s0Witnesses := unpackWitnesses s0StockWords [3590, 265731, 529923]
def s0Index (i : Nat) : Nat := unpack 0x9 2 i
def s0Codes (i : Nat) : Nat := unpack 0x7 15 i
def s0Forest (i : Nat) : Nat := unpack 0xe 14 i
def s0Links := pageLinks s0Index s0Codes 1 13 1 2
def s0Data (i : Nat) : Nat × Nat :=
  let e := s0Forest i
  (e &&& 1, e >>> 1)
def s0Sample : Nat × Nat := (s0Blob175105, 16)
def s0Tags := dagTraceTags s0Mask 16 (dagTagBases s0StockWords s0Blob175230 s0Blob175271 16) 3 s0Data
def s0States := dagTrace s0Mask s0StockWords 3 s0Data
def s0MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s0Moves := dagMoves s0MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Autos : DagMovesOK s0Mask s0Goal 64 s0Moves := dagMovesOfCheck (by decide +kernel)
def s0Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack 0x0 1 (i % 16)
def s0Check := dagCheckNode s0Mask s0Goal s0Chart (fun i => dagKnownCloses s0Goal (cutPick s0Cuts (s0Choice i))) 1 s0States s0Moves s0Links s0Sample s0Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Roots : dagCheckRoots s0Mask s0Goal s0Chart (dagKnownCloses s0Goal s0Cuts) s0Witnesses (dagRef 1 s0States s0Moves s0Links 0) s0StockWords 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Block0 : treeBlock 0 1 s0Check = true := by decide +kernel
theorem s0Blocks : treeBlock 0 1 s0Check = true := s0Block0
theorem s0Known : Known s0Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s0Stock : Lower s0Mask s0StockWords s0Goal 4 := by
  apply lowerDag s0Choice _ _ _ _ s0Autos _ _ _ s0Known _ s0Roots s0Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s0Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def st23 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf00ff00ff00ff00f,0),(0xf000f000f000f0,4)],[(0xf000f000f000f00,4)])
def pm0 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23]
def st02 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xa5a5a5a5a5a5a5a5,0),(0xa0a0a0a0a0a0a0a,3)],[(0x5050505050505050,3)])
def pm1 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02]
def st03 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xaa55aa55aa55aa55,0),(0xaa00aa00aa00aa,7)],[(0x5500550055005500,7)])
def pm2 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02, st03]
def pm3 : List (List (Nat × Nat) × List (Nat × Nat)) := [st03, st02]
def s1Blob178817 : Nat := (cbits [0x2c060b0301c0607,0x86433050380c0e05,0x40b0101c643a190d,0xf0303c060f010380,0x90dc0c36018cc140,0x1c643e190ec143a1,0x40f018380c0b050,0x37018dc0436010cc,0x50ec063b010e80c,0x1c643f050f80c3e,0xc0c3319038640b19,0x437050d80636050c,0xe010ec0c3a018e80,0x50fc0c3f018fc043,0xf80c3b050dc640f0,0x43f018])
def s1Blob179158 : Nat := (cbits [0x59dfa4dcdb6af64f,0x1f4f37e3978ed9bd,0xc3f0381dfe0df877,0xf7ff8ff])
def s1Blob179264 : Nat := (cbits [0x920890048809005,0x100a088820882090,0x340380280a0a009,0x800780])
def s1Mask : Nat := 0xcccc00000000cccc
abbrev s1Goal : Nat := sGoal &&& s1Mask
abbrev s1StockWords : List Nat := [0x8888000000008888,0xc0c000000000c0c0,0xcc0000000000cc00,0xcccc000000000000]
def s1Fact : Nat × List Nat × Nat × Nat := (s1Mask, s1StockWords, 7, s1Goal)
def s1Cuts : List (Nat × List Nat × Nat × Nat) := [s0Fact]
def s1Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 11, 14, 51, 54, 58, 7, 11, 14, 51, 54, 58, 3, 6, 10, 50, 3, 6, 10, 50, 3, 6, 10, 50], rfl⟩
def s1Witnesses := unpackWitnesses s1StockWords [3590, 265731, 529923, 812547]
def s1Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x4028050088c18001,0x44c8180b005c2a0d,0x84308200b656]) else 0x9c730622440) 11 (i % 16)
def s1Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x820024040100000f,0xc940361601305007,0xa823141001595807,0xb8b18fc28c6d1062,0x5b2188584c40a032,0x7031]) else (if j < 2 then (cbits [0x111880086282492c,0x200680c02803496,0x81201007008050c7,0xa0a0060480a01c03,0xb260ca83806c1802,0x4e19]) else (cbits [0x700483c0501a01c,0xc4c52223292e00f,0x8866200318a07804,0x18d25]))) 21 (i % 16)
def s1Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x60862820040401e0,0xc050600784012149,0x3860082406860081,0xc00e34054c009846,0x143c06c]) else 0x12581194c40561) 18 (i % 16)
def s1Links := pageLinks s1Index s1Codes 5 13 5 6
def s1Data (i : Nat) : Nat × Nat :=
  let e := s1Forest i
  (e &&& 31, e >>> 5)
def s1Sample : Nat × Nat := (s1Blob178817, 55)
def s1Tags := dagTraceTags s1Mask 55 (dagTagBases s1StockWords s1Blob179158 s1Blob179264 55) 6 s1Data
def s1States := dagTrace s1Mask s1StockWords 6 s1Data
def s1MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val))), (pm1, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 1, 0, 3, 4, 5] 0 i.val))), (pm2, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val))), (pm3, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [2, 1, 3, 0, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [3, 1, 0, 2, 4, 5] 0 i.val)))]
def s1Moves := dagMoves s1MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Autos : DagMovesOK s1Mask s1Goal 64 s1Moves := dagMovesOfCheck (by decide +kernel)
def s1Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then 0x3 else 0x5) 1 (i % 16)
def s1Check := dagCheckNode s1Mask s1Goal s1Chart (fun i => dagKnownCloses s1Goal (cutPick s1Cuts (s1Choice i))) 19 s1States s1Moves s1Links s1Sample s1Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Roots : dagCheckRoots s1Mask s1Goal s1Chart (dagKnownCloses s1Goal s1Cuts) s1Witnesses (dagRef 19 s1States s1Moves s1Links 0) s1StockWords 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Block0 : treeBlock 0 19 s1Check = true := by decide +kernel
theorem s1Blocks : treeBlock 0 19 s1Check = true := s1Block0
theorem s1Known : Known s1Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s0Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s1Stock : Lower s1Mask s1StockWords s1Goal 7 := by
  apply lowerDag s1Choice _ _ _ _ s1Autos _ _ _ s1Known _ s1Roots s1Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s1Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def st24 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf0f00f0ff0f00f0f,0),(0xf0f00000f0f0,12)],[(0xf0f00000f0f0000,12)])
def pm4 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24]
def st25 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xf0f0f0f00f0f0f0f,0),(0xf0f0f0f0,28)],[(0xf0f0f0f00000000,28)])
def pm5 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24, st25]
def s2Blob182941 : Nat := (cbits [0x4c06130301c0607,0xc44230188c2c1709,0xc360b0d864331309,0x70b01c0407190d84,0x904c2c130104c4c0,0x8c24170305c06171,0x6271908c4c23010,0x33018cc44270309c,0x90d80c36110cc24,0xdc4c370b0dc4436,0xc0c131101c240719,0x4171305c04171104,0x70109c24230308c6,0xb0cc04331909c2c2,0xdc0637010d84c330,0x6407110dc2437030,0x270b08c44171304c,0x10dc0636030cc24])
def s2Blob183331 : Nat := (cbits [0xbff7fffe3ffff1ff,0xd5f8e73fc71c7e93,0xe6ff07cff81f8f1c,0xf8fff80fffe00fe0])
def s2Blob183446 : Nat := (cbits [0x4010000009040025,0x2a264a4642496692,0x1942d41a90932b18,0x78486ad24c24dc0])
def s2Mask : Nat := 0xcc00cc00cc00cc
abbrev s2Goal : Nat := sGoal &&& s2Mask
abbrev s2StockWords : List Nat := [0x88008800880088,0xc000c000c000c0,0xcc000000cc0000,0xcc00cc00000000]
def s2Fact : Nat × List Nat × Nat × Nat := (s2Mask, s2StockWords, 6, s2Goal)
def s2Cuts : List (Nat × List Nat × Nat × Nat) := []
def s2Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 19, 35, 54, 7, 19, 35, 54, 7, 19, 35, 54, 3, 22, 38, 50, 3, 22, 38, 50, 3, 22, 38, 50], rfl⟩
def s2Witnesses := unpackWitnesses s2StockWords [3590, 265731, 534019, 804355]
def s2Index (i : Nat) : Nat := unpack 0xa28301 6 i
def s2Codes (i : Nat) : Nat := unpack (cbits [0x31010c504010000f,0x1492c6]) 17 i
def s2Forest (i : Nat) : Nat := unpack 0x3144010803c 15 i
def s2Links := pageLinks s2Index s2Codes 3 13 2 4
def s2Data (i : Nat) : Nat × Nat :=
  let e := s2Forest i
  (e &&& 3, e >>> 2)
def s2Sample : Nat × Nat := (s2Blob182941, 64)
def s2Tags := dagTraceTags s2Mask 64 (dagTagBases s2StockWords s2Blob183331 s2Blob183446 64) 5 s2Data
def s2States := dagTrace s2Mask s2StockWords 5 s2Data
def s2MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm4, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 2, 5] 0 i.val))), (pm5, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 5, 3, 2, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 3, 5, 2] 0 i.val)))]
def s2Moves := dagMoves s2MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Autos : DagMovesOK s2Mask s2Goal 64 s2Moves := dagMovesOfCheck (by decide +kernel)
def s2Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack 0x0 1 (i % 16)
def s2Check := dagCheckNode s2Mask s2Goal s2Chart (fun i => dagKnownCloses s2Goal (cutPick s2Cuts (s2Choice i))) 3 s2States s2Moves s2Links s2Sample s2Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Roots : dagCheckRoots s2Mask s2Goal s2Chart (dagKnownCloses s2Goal s2Cuts) s2Witnesses (dagRef 3 s2States s2Moves s2Links 0) s2StockWords 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Block0 : treeBlock 0 3 s2Check = true := by decide +kernel
theorem s2Blocks : treeBlock 0 3 s2Check = true := s2Block0
theorem s2Known : Known s2Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s2Stock : Lower s2Mask s2StockWords s2Goal 6 := by
  apply lowerDag s2Choice _ _ _ _ s2Autos _ _ _ s2Known _ s2Roots s2Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s2Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s3Mask : Nat := 0xc0c0c0c0c0c0c0c
abbrev s3Goal : Nat := sGoal &&& s3Mask
abbrev s3StockWords : List Nat := [0x808080808080808,0xc000c000c000c00,0xc0c00000c0c0000,0xc0c0c0c00000000]
def s3Fact : Nat × List Nat × Nat × Nat := (s3Mask, s3StockWords, 6, s3Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s3Stock : Lower s3Mask s3StockWords s3Goal 6 := dagShiftLower (width := 64) pm0 s2Stock (by decide +kernel)
def s4Mask : Nat := 0xcccccccc
abbrev s4Goal : Nat := sGoal &&& s4Mask
abbrev s4StockWords : List Nat := [0x88888888,0xc0c0c0c0,0xcc00cc00,0xcccc0000]
def s4Fact : Nat × List Nat × Nat × Nat := (s4Mask, s4StockWords, 5, s4Goal)
def s4Witnesses := unpackWitnesses s4StockWords [3590, 265731, 529923, 796163]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s4Stock : Lower s4Mask s4StockWords s4Goal 5 := by
  apply essentialLift (witnesses := s4Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
def st45 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xffff00000000ffff,0),(0xffff0000,16)],[(0xffff00000000,16)])
def pm6 : List (List (Nat × Nat) × List (Nat × Nat)) := [st45]
def s5Mask : Nat := 0xcccc0000cccc
abbrev s5Goal : Nat := sGoal &&& s5Mask
abbrev s5StockWords : List Nat := [0x888800008888,0xc0c00000c0c0,0xcc000000cc00,0xcccc00000000]
def s5Fact : Nat × List Nat × Nat × Nat := (s5Mask, s5StockWords, 5, s5Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s5Stock : Lower s5Mask s5StockWords s5Goal 5 := dagShiftLower (width := 64) pm6 s4Stock (by decide +kernel)
def s6Blob190330 : Nat := (cbits [0xb41a2d0e0741a1d,0x4181d160f0383c16,0x83d068f4183c060b,0xc0e0b4581d160f43,0x60f41a3])
def s6Blob190455 : Nat := 0xefbcdf73becf
def s6Blob190496 : Nat := 0x182824124205
def s6Mask : Nat := 0x3000300030003000
abbrev s6Goal : Nat := sGoal &&& s6Mask
abbrev s6StockWords : List Nat := [0x2000200020002000,0x3000000030000000,0x3000300000000000]
def s6Fact : Nat × List Nat × Nat × Nat := (s6Mask, s6StockWords, 4, s6Goal)
def s6Cuts : List (Nat × List Nat × Nat × Nat) := []
def s6Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[29, 45, 60, 29, 45, 60, 29, 45, 60, 29, 45, 60, 13, 28, 44, 13, 28, 44, 13, 28, 44, 13, 28, 44], rfl⟩
def s6Witnesses := unpackWitnesses s6StockWords [14876, 277005, 547341]
def s6Index (i : Nat) : Nat := unpack 0x9 2 i
def s6Codes (i : Nat) : Nat := unpack 0x7 15 i
def s6Forest (i : Nat) : Nat := unpack 0xe 14 i
def s6Links := pageLinks s6Index s6Codes 1 13 1 2
def s6Data (i : Nat) : Nat × Nat :=
  let e := s6Forest i
  (e &&& 1, e >>> 1)
def s6Sample : Nat × Nat := (s6Blob190330, 16)
def s6Tags := dagTraceTags s6Mask 16 (dagTagBases s6StockWords s6Blob190455 s6Blob190496 16) 3 s6Data
def s6States := dagTrace s6Mask s6StockWords 3 s6Data
def s6MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s6Moves := dagMoves s6MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Autos : DagMovesOK s6Mask s6Goal 64 s6Moves := dagMovesOfCheck (by decide +kernel)
def s6Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack 0x0 1 (i % 16)
def s6Check := dagCheckNode s6Mask s6Goal s6Chart (fun i => dagKnownCloses s6Goal (cutPick s6Cuts (s6Choice i))) 1 s6States s6Moves s6Links s6Sample s6Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Roots : dagCheckRoots s6Mask s6Goal s6Chart (dagKnownCloses s6Goal s6Cuts) s6Witnesses (dagRef 1 s6States s6Moves s6Links 0) s6StockWords 3 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Block0 : treeBlock 0 1 s6Check = true := by decide +kernel
theorem s6Blocks : treeBlock 0 1 s6Check = true := s6Block0
theorem s6Known : Known s6Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s6Stock : Lower s6Mask s6StockWords s6Goal 4 := by
  apply lowerDag s6Choice _ _ _ _ s6Autos _ _ _ s6Known _ s6Roots s6Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s6Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def st01 : List (Nat × Nat) × List (Nat × Nat) := ([( 0x9999999999999999,0),(0x2222222222222222,1)],[(0x4444444444444444,1)])
def st34 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xff0000ffff0000ff,0),(0xff000000ff00,8)],[(0xff000000ff0000,8)])
def pm7 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st02, st34]
def s7Mask : Nat := 0x4444000044440000
abbrev s7Goal : Nat := sGoal &&& s7Mask
abbrev s7StockWords : List Nat := [0x4040000040400000,0x4400000044000000,0x4444000000000000]
def s7Fact : Nat × List Nat × Nat × Nat := (s7Mask, s7StockWords, 4, s7Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s7Stock : Lower s7Mask s7StockWords s7Goal 4 := dagShiftLower (width := 64) pm7 s6Stock (by decide +kernel)
def s8Mask : Nat := 0x4444444444444444
abbrev s8Goal : Nat := sGoal &&& s8Mask
abbrev s8StockWords : List Nat := [0x4040404040404040,0x4400440044004400,0x4444000044440000,0x4444444400000000]
def s8Fact : Nat × List Nat × Nat × Nat := (s8Mask, s8StockWords, 5, s8Goal)
def s8Witnesses := unpackWitnesses s8StockWords [7178, 269318, 551974, 814102]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s8Stock : Lower s8Mask s8StockWords s8Goal 5 := by
  apply essentialLift (witnesses := s8Witnesses) (cut := s7Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s7StockWords) (by decide +kernel)
  · exact s7Stock
  · decide +kernel
def s9Mask : Nat := 0xcccc0000cccc0000
abbrev s9Goal : Nat := sGoal &&& s9Mask
abbrev s9StockWords : List Nat := [0x8888000088880000,0xc0c00000c0c00000,0xcc000000cc000000,0xcccc000000000000]
def s9Fact : Nat × List Nat × Nat × Nat := (s9Mask, s9StockWords, 5, s9Goal)
def s9Witnesses := unpackWitnesses s9StockWords [9746, 277530, 539670, 814102]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s9Stock : Lower s9Mask s9StockWords s9Goal 5 := by
  apply essentialLift (witnesses := s9Witnesses) (cut := s7Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s7StockWords) (by decide +kernel)
  · exact s7Stock
  · decide +kernel
def s10Mask : Nat := 0xcccccccc00000000
abbrev s10Goal : Nat := sGoal &&& s10Mask
abbrev s10StockWords : List Nat := [0x8888888800000000,0xc0c0c0c000000000,0xcc00cc0000000000,0xcccc000000000000]
def s10Fact : Nat × List Nat × Nat × Nat := (s10Mask, s10StockWords, 5, s10Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s10Stock : Lower s10Mask s10StockWords s10Goal 5 := dagShiftLower (width := 64) pm6 s9Stock (by decide +kernel)
def st35 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xff00ff0000ff00ff,0),(0xff00ff00,24)],[(0xff00ff00000000,24)])
def pm8 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st02, st34, st35]
def s11Mask : Nat := 0x4444444400000000
abbrev s11Goal : Nat := sGoal &&& s11Mask
abbrev s11StockWords : List Nat := [0x4040404000000000,0x4400440000000000,0x4444000000000000]
def s11Fact : Nat × List Nat × Nat × Nat := (s11Mask, s11StockWords, 4, s11Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s11Stock : Lower s11Mask s11StockWords s11Goal 4 := dagShiftLower (width := 64) pm8 s6Stock (by decide +kernel)
def pm9 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23, st45]
def s12Blob202182 : Nat := (cbits [0x2c060b0301c0607,0xc0613050380c0e05,0xc1e0d06c2c170904,0x71108c06230d0782,0x50b84c2e150ac4c2,0xd84c360b0d864331,0x643a150e8343a190,0xb1301c2c070101c,0x1038540b0d02c04,0x384c0e0d0382c0e,0xc140f0303c060f15,0x4130d04c2c130104,0xb0905c0c170185c6,0x3078241b0506c061,0x7c2c1f09078141e0,0x54231308c04230d0,0x270309c06271908c,0x110ac142b018ac44,0xbc442e050b80c2e,0xc2433018cc542f13,0x436090d80c36110c,0xa190dc4c370b0dc4,0xd0ec443a090e8143,0xf82c3e190ec543b0,0x643e150f84c3e0d0,0xb1101c24070501c,0x1838440b0902c0c])
def s12Blob202751 : Nat := (cbits [0xfff1fff07e04f3cf,0x8e3b4d337e0e38f8,0x8ff03f1f1c3e387f,0xe03fc07ff1c38e3c,0x1fc0fc0f1ffc01f,0x1ffffe0003fff80,0xffc0000001fff000,0x1ffffff])
def s12Blob202936 : Nat := (cbits [0x2400481000001045,0xc19451280000020,0x1050190908921125,0x4124824a60c28a28,0x256c0f8002a64012,0x253aaa4002392703,0x9380040c49b7e000,0x49cd349c])
def s12Mask : Nat := 0xcccccccccccccccc
abbrev s12Goal : Nat := sGoal &&& s12Mask
abbrev s12StockWords : List Nat := [0x8888888888888888,0xc0c0c0c0c0c0c0c0,0xcc00cc00cc00cc00,0xcccc0000cccc0000,0xcccccccc00000000]
def s12Fact : Nat × List Nat × Nat × Nat := (s12Mask, s12StockWords, 9, s12Goal)
def s12Cuts : List (Nat × List Nat × Nat × Nat) := [s1Fact, s2Fact, s3Fact, s4Fact, s5Fact, s8Fact, s9Fact, s10Fact, s0Fact, s7Fact, s11Fact]
def s12Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 11, 14, 19, 35, 54, 58, 7, 11, 14, 19, 35, 3, 22, 26, 38, 42, 50, 3, 22, 26, 38, 42, 50], rfl⟩
def s12Witnesses := unpackWitnesses s12StockWords [3590, 265731, 529923, 796163, 1066499]
def s12Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x3e01c18b1806a001,0x8804401f18f807c0,0x7849924c02601110,0x3001]) else (cbits [0x6203101880c40601,0xe807023231900c42,0xf00ec67413a01d00,0x3e01])) else (if j < 3 then (cbits [0xa2351028813867d0,0x512a805402a01500,0xe8d740ba05d02e81,0x6002]) else (cbits [0xded6d1350d814c00,0x7e1bf01f04]))) 13 (i % 16)
def s12Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x848024040100001f,0xc5804f1801f0c009,0x8b8037560198e00a,0x72d195940c7c7c62,0xbd698ae7cc40da33,0xed31]) else (cbits [0x99a4ccc925a6092c,0x1c9872e0c383649b,0x9046200518f810c5,0x4661c0424cc1925,0x2230e0112580662,0x431])) else (if j < 3 then (cbits [0x50c781d8710892c,0x22d258166208a195,0x1e32a0d01505002,0x8124960898a840c4,0xe29bd105187e26c3,0xe00]) else (cbits [0xb8070540681c01c,0x2680552e0281a00f,0x303149b4960d988,0x1d18a4c8ca064c4,0xa810c5079e893a62,0xb18]))) else (if j < 6 then (if j < 5 then (cbits [0x8e8cac6c64f2431f,0xc80c40ba3375b199,0xa4692c6231b9118a,0x82749b9324cc9525,0x601988195872c6c3,0x2149]) else (cbits [0x10a4b010c40c2c38,0x43c0220a0082461c,0x5292c11014c7807,0x42c62195b0fca987,0x21724fa88c40d4f4,0x2f7a])) else (if j < 7 then (cbits [0xc98cac4c63e0c314,0xca8c56466205e19b,0x1de937a34963798d,0x824496039880c587,0x452a4b094c4148c3,0x800]) else (if j < 8 then (cbits [0x1a00a65003e28013,0x4d46525631f2618a,0x34c6206e1a0970cd,0x2ee320d718d6d4c5,0xf938c525403c2a01,0x2c18]) else 0x14e620)))) 21 (i % 16)
def s12Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x6314080100807c0,0x2c0863e124b03310,0x80120a4cc261c0e9,0x46804c13101431e2,0x1951a01c3805]) else (cbits [0x1a92c34c5469880d,0x2704068ab0fcd61c,0xcc40c0c51800e2e0,0x8e80ac13102e01e5,0x18a02f447462])) else (if j < 3 then (cbits [0x4062b81259098820,0x338125b030e24496,0x525948c7c149bc09,0x60b10e961fd2c38a,0x7a25c93eb865]) else (cbits [0x8292d058718a4b01,0x3704653a00a74499,0x9]))) 19 (i % 16)
def s12Links := pageLinks s12Index s12Codes 5 13 6 6
def s12Data (i : Nat) : Nat × Nat :=
  let e := s12Forest i
  (e &&& 63, e >>> 6)
def s12Sample : Nat × Nat := (s12Blob202182, 96)
def s12Tags := dagTraceTags s12Mask 96 (dagTagBases s12StockWords s12Blob202751 s12Blob202936 96) 8 s12Data
def s12States := dagTrace s12Mask s12StockWords 8 s12Data
def s12MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val))), (pm9, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 5, 4] 0 i.val)))]
def s12Moves := dagMoves s12MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Autos : DagMovesOK s12Mask s12Goal 64 s12Moves := dagMovesOfCheck (by decide +kernel)
def s12Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x100000000713806,0x31f001000004,0x4008016de0]) else (cbits [0xc000,0xa000000002604fc,0xe20000a770])) else (if j < 3 then (cbits [0x200000001,0x2008010fe002004,0x5338010]) else (cbits [0x103eddc00b57,0xb9c]))) 11 (i % 16)
def s12Check := dagCheckNode s12Mask s12Goal s12Chart (fun i => dagKnownCloses s12Goal (cutPick s12Cuts (s12Choice i))) 55 s12States s12Moves s12Links s12Sample s12Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Roots : dagCheckRoots s12Mask s12Goal s12Chart (dagKnownCloses s12Goal s12Cuts) s12Witnesses (dagRef 55 s12States s12Moves s12Links 0) s12StockWords 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block0 : treeBlock 0 24 s12Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block24 : treeBlock 24 24 s12Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Block48 : treeBlock 48 7 s12Check = true := by decide +kernel
theorem s12Group24_31 : treeBlock 24 31 s12Check = true := treeBlock_merge (start := 24) (left := 24) (right := 7) (check := s12Check) s12Block24 s12Block48
theorem s12Group0_55 : treeBlock 0 55 s12Check = true := treeBlock_merge (start := 0) (left := 24) (right := 31) (check := s12Check) s12Block0 s12Group24_31
theorem s12Blocks : treeBlock 0 55 s12Check = true := s12Group0_55
theorem s12Known : Known s12Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s11Stock) s7Stock) s0Stock) s10Stock) s9Stock) s8Stock) s5Stock) s4Stock) s3Stock) s2Stock) s1Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s12Stock : Lower s12Mask s12StockWords s12Goal 9 := by
  apply lowerDag s12Choice _ _ _ _ s12Autos _ _ _ s12Known _ s12Roots s12Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s12Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def pm10 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st34]
def s13Mask : Nat := 0x5050000050500000
abbrev s13Goal : Nat := sGoal &&& s13Mask
abbrev s13StockWords : List Nat := [0x4040000040400000,0x5000000050000000,0x5050000000000000]
def s13Fact : Nat × List Nat × Nat × Nat := (s13Mask, s13StockWords, 4, s13Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s13Stock : Lower s13Mask s13StockWords s13Goal 4 := dagShiftLower (width := 64) pm10 s6Stock (by decide +kernel)
def pm11 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st24, st23]
def s14Mask : Nat := 0x5500000055000000
abbrev s14Goal : Nat := sGoal &&& s14Mask
abbrev s14StockWords : List Nat := [0x4400000044000000,0x5000000050000000,0x5500000000000000]
def s14Fact : Nat × List Nat × Nat × Nat := (s14Mask, s14StockWords, 4, s14Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s14Stock : Lower s14Mask s14StockWords s14Goal 4 := dagShiftLower (width := 64) pm11 s6Stock (by decide +kernel)
def pm12 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st24, st35]
def s15Mask : Nat := 0x5555000000000000
abbrev s15Goal : Nat := sGoal &&& s15Mask
abbrev s15StockWords : List Nat := [0x4444000000000000,0x5050000000000000,0x5500000000000000]
def s15Fact : Nat × List Nat × Nat × Nat := (s15Mask, s15StockWords, 4, s15Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s15Stock : Lower s15Mask s15StockWords s15Goal 4 := dagShiftLower (width := 64) pm12 s6Stock (by decide +kernel)
def pm13 : List (List (Nat × Nat) × List (Nat × Nat)) := [st35]
def pm14 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23, st25]
def st12 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xc3c3c3c3c3c3c3c3,0),(0xc0c0c0c0c0c0c0c,2)],[(0x3030303030303030,2)])
def pm15 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12]
def pm16 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12, st35]
def st13 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcc33cc33cc33cc33,0),(0xcc00cc00cc00cc,6)],[(0x3300330033003300,6)])
def pm17 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12, st13]
def st15 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcccccccc33333333,0),(0xcccccccc,30)],[(0x3333333300000000,30)])
def pm18 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12, st13, st15]
def pm19 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13, st12]
def pm20 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13, st12, st25]
def pm21 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13, st25]
def s16Blob209908 : Nat := (cbits [0xd8381e0d0782c1e,0x8343a1a0d864360b,0x83c0e0f0703a190e,0xe0a078241e1c0f06,0x80d82836090d8301,0xf0603a0c0e8243a1,0x2c3e180f0303c0a0,0x3e190f8383e0d0f8,0x19078201e1c0f868,0xd820361c078681e,0x8203a1c0d838360d,0x3c1a0e8383a0b0e,0xe190f0343c0b0f02,0x80f8303e0a0f8243,0xf0283a0c0d8601e1,0x203e090])
def s16Blob210252 : Nat := (cbits [0x1fdfc3ffff1ff1ff,0x1ff1f7fe1ffff1ff,0xfff1ff1dfff0ffff,0xf7fff87])
def s16Blob210359 : Nat := (cbits [0x16a078888b0490db,0x12d18845c88a9093,0x1241b602444e8992,0xc44477])
def s16Mask : Nat := 0x5555000055550000
abbrev s16Goal : Nat := sGoal &&& s16Mask
abbrev s16StockWords : List Nat := [0x4444000044440000,0x5050000050500000,0x5500000055000000,0x5555000000000000]
def s16Fact : Nat × List Nat × Nat × Nat := (s16Mask, s16StockWords, 7, s16Goal)
def s16Cuts : List (Nat × List Nat × Nat × Nat) := [s7Fact, s13Fact, s14Fact, s15Fact]
def s16Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[30, 54, 58, 60, 30, 54, 58, 60, 30, 54, 58, 60, 22, 26, 28, 50, 52, 56, 22, 26, 28, 50, 52, 56], rfl⟩
def s16Witnesses := unpackWitnesses s16StockWords [15388, 277530, 539670, 814102]
def s16Index (i : Nat) : Nat := unpack 0x4c242e4702cc3401 9 i
def s16Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0xb0600f020080000f,0x1b42314360272601,0x6276262096327863,0x4620043147292ca6,0x18332083263492c2]) else 0xa6245863248626) 20 (i % 16)
def s16Forest (i : Nat) : Nat := unpack (cbits [0x7918a200410078,0x31251934]) 16 i
def s16Links := pageLinks s16Index s16Codes 4 13 3 5
def s16Data (i : Nat) : Nat × Nat :=
  let e := s16Forest i
  (e &&& 7, e >>> 3)
def s16Sample : Nat × Nat := (s16Blob209908, 55)
def s16Tags := dagTraceTags s16Mask 55 (dagTagBases s16StockWords s16Blob210252 s16Blob210359 55) 6 s16Data
def s16States := dagTrace s16Mask s16StockWords 6 s16Data
def s16MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm13, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 4, 3] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 4, 3] 0 i.val))), (pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val))), (pm14, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 5, 2, 4, 3] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 5, 4, 2] 0 i.val))), (pm15, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val))), (pm16, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 5, 4, 3] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 5, 4, 3] 0 i.val))), (pm17, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 1, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 3, 1, 4, 5] 0 i.val))), (pm18, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 5, 1, 2, 4, 3] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 3, 5, 4, 1] 0 i.val))), (pm19, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 3, 1, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 1, 2, 4, 5] 0 i.val))), (pm20, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 5, 1, 4, 3] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 1, 5, 4, 2] 0 i.val))), (pm21, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 5, 1, 4, 2] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 5, 1, 4, 2] 0 i.val)))]
def s16Moves := dagMoves s16MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Autos : DagMovesOK s16Mask s16Goal 64 s16Moves := dagMovesOfCheck (by decide +kernel)
def s16Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack 0x101f 4 (i % 16)
def s16Check := dagCheckNode s16Mask s16Goal s16Chart (fun i => dagKnownCloses s16Goal (cutPick s16Cuts (s16Choice i))) 6 s16States s16Moves s16Links s16Sample s16Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Roots : dagCheckRoots s16Mask s16Goal s16Chart (dagKnownCloses s16Goal s16Cuts) s16Witnesses (dagRef 6 s16States s16Moves s16Links 0) s16StockWords 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Block0 : treeBlock 0 6 s16Check = true := by decide +kernel
theorem s16Blocks : treeBlock 0 6 s16Check = true := s16Block0
theorem s16Known : Known s16Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s15Stock) s14Stock) s13Stock) s7Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s16Stock : Lower s16Mask s16StockWords s16Goal 7 := by
  apply lowerDag s16Choice _ _ _ _ s16Autos _ _ _ s16Known _ s16Roots s16Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s16Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s17Mask : Nat := 0x5555555555555555
abbrev s17Goal : Nat := sGoal &&& s17Mask
abbrev s17StockWords : List Nat := [0x4444444444444444,0x5050505050505050,0x5500550055005500,0x5555000055550000,0x5555555500000000]
def s17Fact : Nat × List Nat × Nat × Nat := (s17Mask, s17StockWords, 8, s17Goal)
def s17Witnesses := unpackWitnesses s17StockWords [7180, 269322, 531462, 814118, 1076246]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s17Stock : Lower s17Mask s17StockWords s17Goal 8 := by
  apply essentialLift (witnesses := s17Witnesses) (cut := s16Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s16StockWords) (by decide +kernel)
  · exact s16Stock
  · decide +kernel
def pm22 : List (List (Nat × Nat) × List (Nat × Nat)) := [st34]
def pm23 : List (List (Nat × Nat) × List (Nat × Nat)) := [st34, st35]
def pm24 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23, st24]
def pm25 : List (List (Nat × Nat) × List (Nat × Nat)) := [st23, st24, st25]
def pm26 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24, st23]
def pm27 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24, st23, st35]
def pm28 : List (List (Nat × Nat) × List (Nat × Nat)) := [st24, st35]
def s18Blob219147 : Nat := (cbits [0x88c06130182c0607,0x683c160f0383c01,0x60f0402c08071c0f,0x70185c20130603c0,0xe07c301b0186c281,0xac48270189c40230,0x633160bc502b018,0x3c1c0ec6837180cc,0x120f0303c0a0f018,0x1c0007180f0503c,0xc000b1201c280706,0x80f1402c300b0602,0x31603c380f0403c0,0x804c30130a04c001,0x5c38170805c08171,0x381b0806c101b1a0,0x1f0607c061f1c06c,0x1208c00230c07c28,0x9c08271808c5023,0xc102b1a09c582710,0x62f1c0ac582b100a,0x3140bc482f060bc0,0xc0cc6833100cc203,0xdc48370a0dc06371,0x503b0c0ec063b180,0x3c040f0083c180ec,0x160fc383f100f020])
def s18Blob219719 : Nat := (cbits [0xfffffffc0fffff0f,0xf49a6df1c3ffffff,0xfc3c3c3c3c3c3c3f,0x3fc03fc3f8e38ef2,0xff03f0f4ffc03fc0,0xffffc0003fffc003,0xc0000003fffc00f8,0xffffffff])
def s18Blob219907 : Nat := (cbits [0x40000000128a40f,0xb492497000440400,0xc41919349934b4b8,0x2b513b8958c30ab0,0x6e0350d0c9822b51,0x52ab422233bb9112,0x822222238ed400e0,0xa333b3bb])
def s18Mask : Nat := 0x9999999999999999
abbrev s18Goal : Nat := sGoal &&& s18Mask
abbrev s18StockWords : List Nat := [0x8888888888888888,0x9090909090909090,0x9900990099009900,0x9999000099990000,0x9999999900000000]
def s18Fact : Nat × List Nat × Nat × Nat := (s18Mask, s18StockWords, 8, s18Goal)
def s18Cuts : List (Nat × List Nat × Nat × Nat) := []
def s18Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 11, 19, 35, 60, 7, 11, 19, 35, 60, 7, 11, 3, 28, 44, 52, 56, 3, 28, 44, 52, 56, 3, 28], rfl⟩
def s18Witnesses := unpackWitnesses s18StockWords [3588, 265731, 529923, 796163, 1066499]
def s18Index (i : Nat) : Nat := unpack (cbits [0x40480900f941f001,0xc1516a04e39c120e,0xc03802f0de0b]) 11 i
def s18Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x820024040100001f,0xcd40360e01305007,0x68e02b450139b807,0x50918a2b80dd5406,0x3870c7c306361631,0x1c19]) else (cbits [0x170cdcb06663c32b,0xdb0c4e7662139310,0x8fc6377c319b718a,0x78c499a5a4b52525,0x42db0e5658711c93,0x200])) else (if j < 3 then (cbits [0x21a4b0ccc4006314,0x580680c0285361c,0x8306300831213010,0x318a010020a0c7,0x41530e0692581462,0xd31]) else 0x1a318)) 21 (i % 16)
def s18Forest (i : Nat) : Nat := unpack (cbits [0x8a100208010201f0,0x9880a1801e200911,0x8988286282624800,0xc7c4c51a31b118a]) 17 i
def s18Links := pageLinks s18Index s18Codes 5 13 4 6
def s18Data (i : Nat) : Nat × Nat :=
  let e := s18Forest i
  (e &&& 15, e >>> 4)
def s18Sample : Nat × Nat := (s18Blob219147, 96)
def s18Tags := dagTraceTags s18Mask 96 (dagTagBases s18StockWords s18Blob219719 s18Blob219907 96) 7 s18Data
def s18States := dagTrace s18Mask s18StockWords 7 s18Data
def s18MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm22, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 3, 5] 0 i.val))), (pm23, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 5, 3, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 4, 5, 3] 0 i.val))), (pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val))), (pm24, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 2, 3, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 4, 2, 5] 0 i.val))), (pm25, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 5, 2, 3, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 4, 5, 2] 0 i.val))), (pm26, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 4, 2, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 2, 3, 5] 0 i.val))), (pm27, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 5, 2, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 2, 5, 3] 0 i.val))), (pm28, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 5, 2, 3] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 4, 5, 2, 3] 0 i.val)))]
def s18Moves := dagMoves s18MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Autos : DagMovesOK s18Mask s18Goal 64 s18Moves := dagMovesOfCheck (by decide +kernel)
def s18Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack 0x0 1 (i % 16)
def s18Check := dagCheckNode s18Mask s18Goal s18Chart (fun i => dagKnownCloses s18Goal (cutPick s18Cuts (s18Choice i))) 15 s18States s18Moves s18Links s18Sample s18Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Roots : dagCheckRoots s18Mask s18Goal s18Chart (dagKnownCloses s18Goal s18Cuts) s18Witnesses (dagRef 15 s18States s18Moves s18Links 0) s18StockWords 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Block0 : treeBlock 0 15 s18Check = true := by decide +kernel
theorem s18Blocks : treeBlock 0 15 s18Check = true := s18Block0
theorem s18Known : Known s18Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s18Stock : Lower s18Mask s18StockWords s18Goal 8 := by
  apply lowerDag s18Choice _ _ _ _ s18Autos _ _ _ s18Known _ s18Roots s18Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s18Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s19Blob224401 : Nat := (cbits [0xd8180e050380c0e,0x703a190e8683619,0x80e01038703c1a0f,0xa180d80c36040380,0x80f0183c180e8143,0x38703e1a0f8643e1,0x7036020d80436000,0x3c1a0e8103a010e8,0x30f8643c040f008,0x38603e060f8143e,0x800361c038680e19,0xc3a000e81836050d,0xc030f0003c060e80,0x40f8083e010f8143,0xf0083a040d8600e0,0x3e010])
def s19Blob224742 : Nat := (cbits [0xcfdf8fff8ffcfe7f,0xf3f9f7f8fff8ff9f,0xfbfe3f1dff8fff8f,0xf7ff8ff])
def s19Blob224849 : Nat := (cbits [0x4aa0e489c244522b,0x52518896894c448a,0x23d43f029268c944,0x800789])
def s19Mask : Nat := 0x5555000000005555
abbrev s19Goal : Nat := sGoal &&& s19Mask
abbrev s19StockWords : List Nat := [0x4444000000004444,0x5050000000005050,0x5500000000005500,0x5555000000000000]
def s19Fact : Nat × List Nat × Nat × Nat := (s19Mask, s19StockWords, 7, s19Goal)
def s19Cuts : List (Nat × List Nat × Nat × Nat) := [s15Fact]
def s19Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[14, 54, 58, 60, 14, 54, 58, 60, 14, 54, 58, 60, 6, 10, 12, 50, 52, 56, 6, 10, 12, 50, 52, 56], rfl⟩
def s19Witnesses := unpackWitnesses s19StockWords [7180, 269322, 531462, 814086]
def s19Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x4028050088c18001,0xd85b0360644a15,0x802e8dd03817]) else 0x9c730622421) 11 (i % 16)
def s19Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x820024040100000f,0xc940361a01305007,0xa823141001396807,0x78d18fc28c6d1062,0x3b2188584c40a032,0x7031]) else (if j < 2 then (cbits [0x111880086282492c,0x82464c0c31c03496,0x9663249313058cc,0xa312040c901c63,0x8071890180181863,0xf31]) else (cbits [0x58c68200180e00c,0xc5262226312b193,0x8866200318a060c9,0x18d25]))) 21 (i % 16)
def s19Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x60862820040401e0,0xc638600784012149,0x48a19318648718c1,0xe00984c60c19918c,0x31838c48]) else 0x12581318c404e1) 18 (i % 16)
def s19Links := pageLinks s19Index s19Codes 5 13 5 6
def s19Data (i : Nat) : Nat × Nat :=
  let e := s19Forest i
  (e &&& 31, e >>> 5)
def s19Sample : Nat × Nat := (s19Blob224401, 55)
def s19Tags := dagTraceTags s19Mask 55 (dagTagBases s19StockWords s19Blob224742 s19Blob224849 55) 6 s19Data
def s19States := dagTrace s19Mask s19StockWords 6 s19Data
def s19MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val))), (pm15, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val))), (pm17, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 1, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 3, 1, 4, 5] 0 i.val))), (pm19, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 3, 1, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 3, 1, 2, 4, 5] 0 i.val)))]
def s19Moves := dagMoves s19MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Autos : DagMovesOK s19Mask s19Goal 64 s19Moves := dagMovesOfCheck (by decide +kernel)
def s19Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then 0x3 else 0x5) 1 (i % 16)
def s19Check := dagCheckNode s19Mask s19Goal s19Chart (fun i => dagKnownCloses s19Goal (cutPick s19Cuts (s19Choice i))) 19 s19States s19Moves s19Links s19Sample s19Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Roots : dagCheckRoots s19Mask s19Goal s19Chart (dagKnownCloses s19Goal s19Cuts) s19Witnesses (dagRef 19 s19States s19Moves s19Links 0) s19StockWords 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Block0 : treeBlock 0 19 s19Check = true := by decide +kernel
theorem s19Blocks : treeBlock 0 19 s19Check = true := s19Block0
theorem s19Known : Known s19Cuts := (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s15Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s19Stock : Lower s19Mask s19StockWords s19Goal 7 := by
  apply lowerDag s19Choice _ _ _ _ s19Autos _ _ _ s19Known _ s19Roots s19Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s19Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl <;> decide +kernel
def s20Mask : Nat := 0x5555555500000000
abbrev s20Goal : Nat := sGoal &&& s20Mask
abbrev s20StockWords : List Nat := [0x4444444400000000,0x5050505000000000,0x5500550000000000,0x5555000000000000]
def s20Fact : Nat × List Nat × Nat × Nat := (s20Mask, s20StockWords, 7, s20Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s20Stock : Lower s20Mask s20StockWords s20Goal 7 := dagShiftLower (width := 64) pm6 s16Stock (by decide +kernel)
def s21Mask : Nat := 0x5050505050505050
abbrev s21Goal : Nat := sGoal &&& s21Mask
abbrev s21StockWords : List Nat := [0x4040404040404040,0x5000500050005000,0x5050000050500000,0x5050505000000000]
def s21Fact : Nat × List Nat × Nat × Nat := (s21Mask, s21StockWords, 5, s21Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s21Stock : Lower s21Mask s21StockWords s21Goal 5 := dagShiftLower (width := 64) pm15 s8Stock (by decide +kernel)
def s22Mask : Nat := 0x5500550055005500
abbrev s22Goal : Nat := sGoal &&& s22Mask
abbrev s22StockWords : List Nat := [0x4400440044004400,0x5000500050005000,0x5500000055000000,0x5500550000000000]
def s22Fact : Nat × List Nat × Nat × Nat := (s22Mask, s22StockWords, 5, s22Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s22Stock : Lower s22Mask s22StockWords s22Goal 5 := dagShiftLower (width := 64) pm17 s8Stock (by decide +kernel)
def s23Blob234250 : Nat := (cbits [0x2c060b0301c0607,0xc180e050380c0e05,0x41b0b05c24130184,0x30e078341e0b0783,0x50ac4c271108c062,0xcc582e150b84c2e1,0x6436130d82c36190,0x3a150e8343a1a0d8,0x160f0383c1c0e864,0x1c04071c0f0683c,0xc040b1301c2c0702,0x40e1502c340b0402,0xe0b038100e020380,0x50384c0e0e038340,0x3c0c0f0183c580e1,0x20130104c180f050,0x171904c34130b04c,0xa05c24170305c06,0x6c241b0506c061b,0x8181e050780c1e0c,0xc1f0c078281e0907,0x30108c381f0d07c2,0x908c54231308c402,0x9c44270309c06271,0x442b050ac062b120,0x2e050b80c2e140ac,0x140b8482e110b818])
def s23Blob234822 : Nat := (cbits [0xfff803fc0023c78f,0x3fffffff03fffc0f,0xfffffffffffffffc,0xf07ffc3fc3dd3a73,0xfc1e3c7cfc3c1ff0,0xffc01fff007fffc3,0xff800003ffe03f80,0xffffc00000001fff,0xffffe00000000003])
def s23Blob235038 : Nat := (cbits [0x1008000000004085,0x1defdfbf00440001,0x2ddfacb77ebb6774,0xa255a839c2d52a52,0xec1a346854289550,0x9a811a6a0466d382,0xcf00e11377603f00,0xbbbf800000021f8c,0xe333c00008070223])
def s23Mask : Nat := 0xdddddddddddddddd
abbrev s23Goal : Nat := sGoal &&& s23Mask
abbrev s23StockWords : List Nat := [0x8888888888888888,0xcccccccccccccccc,0xd0d0d0d0d0d0d0d0,0xdd00dd00dd00dd00,0xdddd0000dddd0000,0xdddddddd00000000]
def s23Fact : Nat × List Nat × Nat × Nat := (s23Mask, s23StockWords, 11, s23Goal)
def s23Cuts : List (Nat × List Nat × Nat × Nat) := [s12Fact, s17Fact, s18Fact, s19Fact, s16Fact, s20Fact, s2Fact, s3Fact, s4Fact, s5Fact, s21Fact, s22Fact]
def s23Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 11, 14, 19, 35, 54, 58, 60, 7, 11, 14, 19, 3, 22, 26, 28, 38, 42, 44, 50, 52, 56, 3, 22], rfl⟩
def s23Witnesses := unpackWitnesses s23StockWords [3590, 269324, 527875, 792067, 1058307, 1328643]
def s23Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x200b8822600c0001,0x43610d043210c803,0x843e20e883a00e0,0x151c4481]) else (cbits [0x2218806201880620,0x86c01a8466219806,0xd807221c047001b0,0x1e847621])) else (if j < 3 then (cbits [0x261098025087cc,0xa092800a002800a,0xd18b402d00b212c8,0x3000c002]) else (if j < 4 then (cbits [0x53384c263080c01,0x8dcd3700dc03684d,0x3810643e98fa03d8,0x43810e04]) else (cbits [0x40448510144010e1,0x11c747011c045111,0x7015c054953ac4aa,0x57015c05])))) else (if j < 8 then (if j < 6 then (cbits [0x41590164059015c4,0x16c05b0166359816,0xe857435d017405b1,0x5f857c15]) else (if j < 7 then (cbits [0xe262898816185803,0x59806601980648d8,0x185b2a672d9a1660,0x7401c847]) else (cbits [0x407501d027401d00,0xde217881e017519d,0xe89f057b09ea1790,0x808dfe27]))) else (if j < 9 then (cbits [0x518502121830e082,0x664195225218dba1,0xd867419a96681998,0xa1067869]) else (if j < 10 then (cbits [0x23a4068a3a206861,0xaac2a722982a6029,0x182c22af8ab45ac0,0xb186c60b]) else (cbits [0x6b3a6ca2b282c81,0x70a0c18b022bb2ee,0xc30b0c0c28]))))) 14 (i % 16)
def s23Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0x6807c0100400003f,0x31083e6208340560,0x3320cc5623989c37,0xb0fa4b19931f9326,0x9949fd329338dd25,0x29187e5130e3]) else (if j < 2 then (cbits [0x2988402310344f44,0x49601462b018c4e0,0x2d00d25902a4b602,0x803a4d20461c0089,0xb19801231402064,0x30628039890]) else (cbits [0x700d809312010624,0x49602a63604cc400,0x3806d26c0d24cc18,0x78c501e61c83ac,0x1231002233204065,0x83d259089894]))) else (if j < 4 then (cbits [0xa30e00f19b424c38,0x18a02c3300400500,0x40065870090cd817,0x88e31201c61e4220,0xf1a0032c3805125,0x8806610009e]) else (if j < 5 then (cbits [0xe8cac0218a24403f,0x49985892d09d2590,0x3f0c587097a4fc2f,0x10bd11317a2066c,0x2461c0460364864a,0x9a4a012bd28]) else (cbits [0x200fe2401985000f,0x31024833f0906679,0x440ad87e14b0e003,0x41680f82a7a2252f,0x1431a8086204b409,0x4ba4a0173d12])))) else (if j < 9 then (if j < 7 then (cbits [0x30cfc21199861250,0x61f85cc390a58709,0x3d0a9e88193d1130,0xa15a4b12502484a0,0x3531e06cc380d126,0x4e00941c00f8]) else (if j < 8 then (cbits [0xf0cdc1319480a314,0x61cc58c380e926d0,0x4450d89621b0fc42,0xa24940467a5888f,0x3b3180732508b587,0x10187c1fa4b0]) else (cbits [0xc940417a2280c4a,0x61c07a92c0f0c40a,0x3c0f52609f3d103e,0x49c8d283f62007c9,0x4592845cf4410588,0x120038030020]))) else (if j < 10 then (cbits [0xf3d106a49a0c401d,0x1942fd250201e963,0x33174c422d988049,0xe2fb0e15e31f8bc6,0x4a00d2bef4418587,0x14862a278c50]) else (if j < 11 then (cbits [0xa0ccc541938a631b,0x3198ae627154c40a,0x381692662c24b157,0x2260c504b0042b0c,0x4e61c09c92c13463,0x140c40260c69]) else (cbits [0x680915161c0a292c,0x61c0ac92c140c402,0x2c144c40270c9956,0x2798a05961c0ac9,0x5149a2b8f4417187,0x1506682918d0]))))) else (if j < 18 then (if j < 15 then (if j < 13 then (cbits [0x3d105c4960b0634,0x31a0b43281652803,0x2019064834a4b063,0x330c50650090d06,0x6849a0ce62419cc4,0x124038038020]) else (if j < 14 then (cbits [0xa0c986b1920c601d,0x49f8f49331e12583,0x441f587e3db0e17a,0xa36004c080042f6f,0x6f18a8da31419003,0x5c0666380c9c]) else (cbits [0x8b0e0734998e292c,0x18e812314194050b,0x205b98703724b066,0x82500707261c0dc6,0x7649f0ec9321d462,0x5dde883bb0e1]))) else (if j < 16 then (cbits [0xa8ca04e19409631c,0x31a2f2f441e58702,0x281d86602b807056,0x3b98c8713180b03,0x5931a0f8f441e587,0x1680383924f0]) else (if j < 17 then (cbits [0xdb1005f1940e6324,0x7a60c06341fe4a03,0x34204c803080707c,0xa0500208219e0fa9,0x1b01ac2a02905403,0x234664420cc0]) else (cbits [0xd24b06a312074620,0x61f926c3e2458711,0x44655896c9b12895,0xcb4940987a592cf,0x1600e90a01302c01,0x2186290b00a4])))) else (if j < 21 then (if j < 19 then (cbits [0x48cfc89199910315,0x4960d66240ecc40c,0x4423187e4530e23b,0xa060c506c498314f,0x3c31042e32905c63,0x8f1258369890]) else (if j < 20 then (cbits [0x724c1877a210ec38,0x3100e09301bd2603,0x381c52601f24b087,0x83930f08b7a247cc,0x7431211c3141ccc4,0x63d89447b0f8]) else (cbits [0xa989190928120f44,0x4980ee9301d8c483,0x3c64a4a0493d1078,0x12024b0403100f2c,0x7a31211e33c2524a,0x240c7c4518f0]))) else (if j < 23 then (if j < 22 then (cbits [0xb0e07b49808292c,0x928328f4a249e892,0x301f187845a52097,0x4d18d87d3121183,0x9f625c86c398bd87,0x26c66050c940]) else (cbits [0xebd109c18a13d250,0x4a1140634274c784,0x2d0c5259183d109e,0xe4b24dc7e4998889,0x4461cc62c3868527,0x28de89d0b0fe])) else (if j < 24 then (cbits [0xfb0fc4561c864c38,0x7a2c64f4425d8863,0x27118c4219988245,0xe5298d4983159006,0x46496c6692c2a0c6,0xaa126f52a4d6]) else (cbits [0xa24b0a619e154c38,0x1a446a92c29c6291,0x8d98701b24b0a9])))))) 23 (i % 16)
def s23Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x9880080100203f00,0x8c420492d0349601,0x23240849a03989c0,0xc1980598ac086281,0x780d83803e023140,0x18a0]) else (cbits [0x18803c6641e3280f,0x8c6c1cc381431007,0x292c0e18a0b8cc05,0xc49b0724cc398703,0xb0e4398701cc3c1,0x3100])) else (if j < 3 then (cbits [0x80cc81e884202720,0xde9446c382301b11,0xf284961049408,0x61f943d10a98705,0x3d10b407c5a92d2,0x4999]) else (if j < 4 then (cbits [0x3d10c98704125030,0xc786a9353461f90,0x203e3831080b0e0d,0xc3181da4d8e24a07,0xdb0e0f1258786203,0x4961]) else (cbits [0x30e4e1e8876c3e3b,0x24a08af443861f9c,0x201c4831380bd2ce,0xb004258069286509,0x524b12c632963144,0x18a2])))) else (if j < 8 then (if j < 6 then (cbits [0xc5529258a062050,0x8c40943274a18da5,0x292c4a313a524b15,0xc31024a4cd29870b,0x498cd24c4292c385,0x61c2]) else (if j < 7 then (cbits [0x80752187e92f4460,0x4024ca3246431a31,0x662064310328c519,0xc19235a4d121258c,0x624b1b8628d80136,0x18ab]) else (cbits [0x30e1c9258d83276c,0x4628ea3266b499b6,0x292c6b61c3aa4c9d,0xc61c35a4cdad870f,0xfbd112187ed6f447,0x9283]))) else (if j < 9 then (cbits [0x8cf208c8102f4b48,0x40270a3308431580,0xa3158561c438c521,0x57a245b0e2146670,0x70c523866508c3f8,0x61f4]) else (if j < 10 then (cbits [0x3d124987108f448e,0x187f092509461f42,0x2f4b849284bbd121,0xc1984d98da68c660,0xd49426de89383149,0x625c]) else (cbits [0xb0e0064a134634a0,0x8c6b4ac3f017a251,0x2637a518a538cf29,0x30e2946915]))))) 21 (i % 16)
def s23Links := pageLinks s23Index s23Codes 5 13 8 6
def s23Data (i : Nat) : Nat × Nat :=
  let e := s23Forest i
  (e &&& 255, e >>> 8)
def s23Sample : Nat × Nat := (s23Blob234250, 96)
def s23Tags := dagTraceTags s23Mask 96 (dagTagBases s23StockWords s23Blob234822 s23Blob235038 96) 10 s23Data
def s23States := dagTrace s23Mask s23StockWords 10 s23Data
def s23MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val))), (pm9, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 5, 4] 0 i.val)))]
def s23Moves := dagMoves s23MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Autos : DagMovesOK s23Mask s23Goal 64 s23Moves := dagMovesOfCheck (by decide +kernel)
def s23Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x30000334b3033033,0xf30000734730f34f,0x40cf14f3000cf3c]) else (cbits [0x30004f3400002cf3,0x82000cf3040c72c7,0xb38c2873e23c374])) else (if j < 3 then (cbits [0x80000004730004f3,0x110410f300000,0xf30000004f30100]) else (if j < 4 then (cbits [0x4f30110b3000,0xf3000bdb0f301000,0x400000400004c54]) else (cbits [0xf34c04c0000000,0x4310f10f37b000,0x10000000000004])))) else (if j < 8 then (if j < 6 then (cbits [0x1010000000000000,0x1000000101000000,0xc10020000000c10]) else (if j < 7 then (cbits [0x324330f3010000,0x7300000000000000,0x410000734]) else (cbits [0x472010000051000,0x1000044100000000,0xf30100000510]))) else (if j < 9 then (cbits [0x2cf7cf3000000070,0xd50000000000c500,0x1cf20100000]) else (if j < 10 then (cbits [0x31b001ff3000,0xb30f35310000f301,0x400000000008949]) else (cbits [0xb1f30330330fb000,0xfb11011000043447,0x1]))))) 12 (i % 16)
def s23Check := dagCheckNode s23Mask s23Goal s23Chart (fun i => dagKnownCloses s23Goal (cutPick s23Cuts (s23Choice i))) 171 s23States s23Moves s23Links s23Sample s23Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Roots : dagCheckRoots s23Mask s23Goal s23Chart (dagKnownCloses s23Goal s23Cuts) s23Witnesses (dagRef 171 s23States s23Moves s23Links 0) s23StockWords 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Block0 : treeBlock 0 24 s23Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Block24 : treeBlock 24 24 s23Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Block48 : treeBlock 48 24 s23Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Block72 : treeBlock 72 24 s23Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Block96 : treeBlock 96 24 s23Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Block120 : treeBlock 120 24 s23Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Block144 : treeBlock 144 24 s23Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Block168 : treeBlock 168 3 s23Check = true := by decide +kernel
theorem s23Group0_48 : treeBlock 0 48 s23Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s23Check) s23Block0 s23Block24
theorem s23Group48_48 : treeBlock 48 48 s23Check = true := treeBlock_merge (start := 48) (left := 24) (right := 24) (check := s23Check) s23Block48 s23Block72
theorem s23Group0_96 : treeBlock 0 96 s23Check = true := treeBlock_merge (start := 0) (left := 48) (right := 48) (check := s23Check) s23Group0_48 s23Group48_48
theorem s23Group96_48 : treeBlock 96 48 s23Check = true := treeBlock_merge (start := 96) (left := 24) (right := 24) (check := s23Check) s23Block96 s23Block120
theorem s23Group144_27 : treeBlock 144 27 s23Check = true := treeBlock_merge (start := 144) (left := 24) (right := 3) (check := s23Check) s23Block144 s23Block168
theorem s23Group96_75 : treeBlock 96 75 s23Check = true := treeBlock_merge (start := 96) (left := 48) (right := 27) (check := s23Check) s23Group96_48 s23Group144_27
theorem s23Group0_171 : treeBlock 0 171 s23Check = true := treeBlock_merge (start := 0) (left := 96) (right := 75) (check := s23Check) s23Group0_96 s23Group96_75
theorem s23Blocks : treeBlock 0 171 s23Check = true := s23Group0_171
theorem s23Known : Known s23Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s22Stock) s21Stock) s5Stock) s4Stock) s3Stock) s2Stock) s20Stock) s16Stock) s19Stock) s18Stock) s17Stock) s12Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s23Stock : Lower s23Mask s23StockWords s23Goal 11 := by
  apply lowerDag s23Choice _ _ _ _ s23Autos _ _ _ s23Known _ s23Roots s23Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s23Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s24Mask : Nat := 0xf000f000f000f0
abbrev s24Goal : Nat := sGoal &&& s24Mask
abbrev s24StockWords : List Nat := [0xa000a000a000a0,0xc000c000c000c0,0xf0000000f00000,0xf000f000000000]
def s24Fact : Nat × List Nat × Nat × Nat := (s24Mask, s24StockWords, 6, s24Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s24Stock : Lower s24Mask s24StockWords s24Goal 6 := dagShiftLower (width := 64) pm15 s2Stock (by decide +kernel)
def s25Blob241412 : Nat := (cbits [0xd81a2d068741a0f,0x40c0f1a0d84c360b,0x82d0b07c1a1f0a07,0x6030d84c2f068bc4,0xa0f41a3d120d8283,0x744c0f0b03c080f1,0xc1f1a0742c1d020,0x2d130b4082d0a07c,0x20d8482f030bc68,0xfc1a3f120f4283d,0xc280f1a0fc4c3f0b,0x81f120740c1d1203,0xd030b4681f1307c0,0xa0bc2c2f020bc282,0xfc4c3d0b0f4083d1,0x680f120fc283f030,0x2f0b0b4481f13074,0x20fc0c3d068d828])
def s25Blob241803 : Nat := (cbits [0xdfffffff7fff1fc7,0xb5e39cfce31cfb79,0xe6fc1f3f83e3e3ba,0xf8ffe03ffc03fc3c])
def s25Blob241919 : Nat := (cbits [0x2000000400010907,0x4a39291829583258,0x194b506912ca42a8,0x7921ab258929430])
def s25Mask : Nat := 0xa050a050a050a050
abbrev s25Goal : Nat := sGoal &&& s25Mask
abbrev s25StockWords : List Nat := [0xa000a000a000a000,0x8040804080408040,0xa0500000a0500000,0xa050a05000000000]
def s25Fact : Nat × List Nat × Nat × Nat := (s25Mask, s25StockWords, 6, s25Goal)
def s25Cuts : List (Nat × List Nat × Nat × Nat) := []
def s25Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[15, 29, 45, 54, 15, 29, 45, 54, 15, 29, 45, 54, 13, 22, 38, 52, 13, 22, 38, 52, 13, 22, 38, 52], rfl⟩
def s25Witnesses := unpackWitnesses s25StockWords [7686, 269837, 539149, 809485]
def s25Index (i : Nat) : Nat := unpack 0xa28a28301 6 i
def s25Codes (i : Nat) : Nat := unpack (cbits [0x31010c504010000f,0x892c3]) 17 i
def s25Forest (i : Nat) : Nat := unpack (cbits [0x310118a100410078,0x4961]) 16 i
def s25Links := pageLinks s25Index s25Codes 3 13 3 4
def s25Data (i : Nat) : Nat × Nat :=
  let e := s25Forest i
  (e &&& 7, e >>> 3)
def s25Sample : Nat × Nat := (s25Blob241412, 64)
def s25Tags := dagTraceTags s25Mask 64 (dagTagBases s25StockWords s25Blob241803 s25Blob241919 64) 5 s25Data
def s25States := dagTrace s25Mask s25StockWords 5 s25Data
def s25MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s25Moves := dagMoves s25MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Autos : DagMovesOK s25Mask s25Goal 64 s25Moves := dagMovesOfCheck (by decide +kernel)
def s25Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack 0x0 1 (i % 16)
def s25Check := dagCheckNode s25Mask s25Goal s25Chart (fun i => dagKnownCloses s25Goal (cutPick s25Cuts (s25Choice i))) 5 s25States s25Moves s25Links s25Sample s25Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Roots : dagCheckRoots s25Mask s25Goal s25Chart (dagKnownCloses s25Goal s25Cuts) s25Witnesses (dagRef 5 s25States s25Moves s25Links 0) s25StockWords 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Block0 : treeBlock 0 5 s25Check = true := by decide +kernel
theorem s25Blocks : treeBlock 0 5 s25Check = true := s25Block0
theorem s25Known : Known s25Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s25Stock : Lower s25Mask s25StockWords s25Goal 6 := by
  apply lowerDag s25Choice _ _ _ _ s25Autos _ _ _ s25Known _ s25Roots s25Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s25Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s26Mask : Nat := 0x3030303030303030
abbrev s26Goal : Nat := sGoal &&& s26Mask
abbrev s26StockWords : List Nat := [0x2020202020202020,0x3000300030003000,0x3030000030300000,0x3030303000000000]
def s26Fact : Nat × List Nat × Nat × Nat := (s26Mask, s26StockWords, 5, s26Goal)
def s26Witnesses := unpackWitnesses s26StockWords [10772, 292916, 535045, 805381]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s26Stock : Lower s26Mask s26StockWords s26Goal 5 := by
  apply essentialLift (witnesses := s26Witnesses) (cut := s6Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s6StockWords) (by decide +kernel)
  · exact s6Stock
  · decide +kernel
def pm29 : List (List (Nat × Nat) × List (Nat × Nat)) := [st02, st01, st34]
def s27Mask : Nat := 0xf000f000f000f000
abbrev s27Goal : Nat := sGoal &&& s27Mask
abbrev s27StockWords : List Nat := [0xa000a000a000a000,0xc000c000c000c000,0xf0000000f0000000,0xf000f00000000000]
def s27Fact : Nat × List Nat × Nat × Nat := (s27Mask, s27StockWords, 5, s27Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s27Stock : Lower s27Mask s27StockWords s27Goal 5 := dagShiftLower (width := 64) pm29 s9Stock (by decide +kernel)
def s28Mask : Nat := 0xf0f00000f0f00000
abbrev s28Goal : Nat := sGoal &&& s28Mask
abbrev s28StockWords : List Nat := [0xa0a00000a0a00000,0xc0c00000c0c00000,0xf0000000f0000000,0xf0f0000000000000]
def s28Fact : Nat × List Nat × Nat × Nat := (s28Mask, s28StockWords, 5, s28Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s28Stock : Lower s28Mask s28StockWords s28Goal 5 := dagShiftLower (width := 64) pm15 s9Stock (by decide +kernel)
def pm30 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12, st45]
def s29Mask : Nat := 0xf0f0f0f000000000
abbrev s29Goal : Nat := sGoal &&& s29Mask
abbrev s29StockWords : List Nat := [0xa0a0a0a000000000,0xc0c0c0c000000000,0xf000f00000000000,0xf0f0000000000000]
def s29Fact : Nat × List Nat × Nat × Nat := (s29Mask, s29StockWords, 5, s29Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s29Stock : Lower s29Mask s29StockWords s29Goal 5 := dagShiftLower (width := 64) pm30 s9Stock (by decide +kernel)
def pm31 : List (List (Nat × Nat) × List (Nat × Nat)) := [st01, st34, st35]
def s30Mask : Nat := 0x5050505000000000
abbrev s30Goal : Nat := sGoal &&& s30Mask
abbrev s30StockWords : List Nat := [0x4040404000000000,0x5000500000000000,0x5050000000000000]
def s30Fact : Nat × List Nat × Nat × Nat := (s30Mask, s30StockWords, 4, s30Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s30Stock : Lower s30Mask s30StockWords s30Goal 4 := dagShiftLower (width := 64) pm31 s6Stock (by decide +kernel)
def s31Blob252972 : Nat := (cbits [0x380c0e0301c0a07,0xc2815028541a0f06,0xc1e0e0741a1d0b05,0x7120940a250e0782,0x30b8582d068b44c2,0xd82c361a0d4582e1,0x583c0e0f06836130,0x70681c08071a0f0,0x6838080e1301c2c,0x384c0e0e0382c0e,0x4180f0303c0a0f16,0x8150b0541a150205,0x70305c0a171a0543,0xa074181d02874281,0x7c281e060780c1e0,0x8250e07c2c1f068,0x25160944c2506894,0x1209c0c270289c68,0xb8482d060b40a2d,0xc1a2f120b8182e03,0x835028d4582f130b,0x60a0d80c36120d42,0xa0dc4c370b0dc483,0xf4483c0a0f0183c1,0x683d160f4383d068,0x3e130f8383e0b0f8,0xa01c18071a0f858])
def s31Blob253541 : Nat := (cbits [0xffe3fff03c09f3f3,0xfc764c9fc1e38fc7,0xfe03f1f8e0fc707f,0xff807fc3878f1c,0x3f80fe03ffc01ff,0x3ffffe0000ffff80,0xff00000003fff000,0x3fffffff])
def s31Blob253726 : Nat := (cbits [0x2220911088009131,0x3032448600200241,0xa01908844442225,0xaa9054a89858b18,0x12d80ec054e40152,0xa74aa40010d24e03,0x9c00080c236f6000,0x399349a4])
def s31Mask : Nat := 0xf0f0f0f0f0f0f0f0
abbrev s31Goal : Nat := sGoal &&& s31Mask
abbrev s31StockWords : List Nat := [0xa0a0a0a0a0a0a0a0,0xc0c0c0c0c0c0c0c0,0xf000f000f000f000,0xf0f00000f0f00000,0xf0f0f0f000000000]
def s31Fact : Nat × List Nat × Nat × Nat := (s31Mask, s31StockWords, 9, s31Goal)
def s31Cuts : List (Nat × List Nat × Nat × Nat) := [s24Fact, s25Fact, s26Fact, s21Fact, s27Fact, s28Fact, s29Fact, s6Fact, s13Fact, s30Fact]
def s31Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 14, 21, 37, 54, 60, 7, 14, 21, 37, 54, 60, 13, 22, 28, 38, 44, 52, 13, 22, 28, 38, 44, 52], rfl⟩
def s31Witnesses := unpackWitnesses s31StockWords [3590, 265733, 531462, 797189, 1067525]
def s31Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0xc1130036b00e8001,0x56015804e413804,0x7805641580560158,0x178c5e01]) else (cbits [0xe21b806451900640,0xc7401c847201c806,0x4107ab1e807a01d0,0x26009802])) else (if j < 3 then (cbits [0xa026049802600980,0x8a0027089a126809,0xba32e80b43282,0x3080c013]) else (cbits [0x263480ca43280c24,0x8e003784de03780d,0xc00f003c00ec2381,0x3c08f003]))) else (if j < 6 then (if j < 5 then (cbits [0xa53d88f413d00f40,0x108041850604104f,0x4011004401100421,0x4c811114]) else (cbits [0x4e113804c8d320,0x1421508140150014,0x5155405501540512,0x57815e05])) else (if j < 7 then (cbits [0x66598166059815e4,0x17415d017405c856,0x7019635dc17605d8,0x67059c06]) else (if j < 8 then (cbits [0x406901a0267859e0,0x1c607181c606945a,0x681da07399ce0719,0x7e0ddaf7]) else (cbits [0x2080060007f85fe0,0x20a380920]))))) 14 (i % 16)
def s31Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x220090080200001f,0x40074360130c003c,0x602b1c009c6601f1,0x8c52860379c00cc8,0x3272e0c7cb031526,0x318cacbe]) else (cbits [0xd4620b18cdebe333,0xa24b2e26373898ac,0xa9373ea4ccf492d3,0x3ef4c39ba30e10,0x315028c500601901,0x48c7c10])) else (if j < 3 then (cbits [0x16620850ccc14327,0x730e0209330724b0,0xc620020c64086208,0x3a0ec3803a4b00,0xc3806a4b00c62006,0x398821a]) else (cbits [0x2431e07b0e01a92c,0xb18802a32a098ca0,0x86200a0c502e92c0,0xd0320280a18a01,0x28090022340400d,0x1000a438]))) else (if j < 6 then (if j < 5 then (cbits [0x4663211188042314,0x2b0e04892c9198f8,0xa31492bd104cc3f1,0x30e03e9330f24b03,0x280f0cd03a3288f,0x1380d03e]) else (cbits [0x400130e004826008,0x6989c56620148c50,0x293317a4b25a6331,0x24b02831497b0e06,0x92c060c5254c3815,0x9630e058])) else (if j < 7 then (cbits [0x546200f0c785cc3e,0xf804860c381624b0,0xc63d1718c4640280,0x24f8689320a80225,0xf441b30fc6ac389a,0x1b80d26a]) else (cbits [0x7a0281e00787201c,0x124b0826201f0100,0xe3141d9880743142,0x8ca07e3402018807,0x620220c50803401d,0x2430f08c])))) else (if j < 12 then (if j < 10 then (if j < 9 then (cbits [0x8ac3c263d1096c3e,0x48cdc8a31423b0f0,0xc00f2530e08e6202,0x8c529e03327809c9,0x327148c742c31502,0x220cac82]) else (cbits [0xa0620a20cde82333,0xaa4cca892d2924b0,0x8c39a930e0ae9372,0xb0e0a292c031882a,0x92c1518a40e620a8,0x29b0e0a2])) else (if j < 11 then (cbits [0xb20322b24c0acc40,0x8c7410314ac80f8,0x6c38ad1908b46361,0xa4c812008adbd10b,0xf442f30e2ba93e2e,0x50022bc]) else (cbits [0xc4f4430b0e0c0011,0x31880c83432d0c50,0x2f443430f8ce93e3,0x8c50ca34132a4f0d,0x327120c7c2e31505,0x230cac84]))) else (if j < 14 then (if j < 13 then (cbits [0xa0620a30cde84333,0x5a4b2cc6373318ac,0x9373724ccda92d3,0x9882dac39b5b0e0e,0xc403630e0a292c06,0x37a4c0de]) else (cbits [0xea01f39bd10e4c3e,0x70c50ee0373b00ac,0xa32b178ca44a31f0,0x9884a4620a60cdc6,0x637b118ccbc62b2d,0x35a4b2d2])) else (if j < 15 then (cbits [0xf2c393c30e2e6937,0x9a4b060635079880,0x86203d8078d8c382,0x30f8da92c3098c4a,0x13080022f2f443e,0x1880744c]) else (if j < 16 then (cbits [0xaa3143f00a46c01f,0x38cd50032b3f8ca4,0x492c371882ce3413,0x3d1108c403e30e10,0x1e1900704e012be,0x40b1306e]) else (cbits [0x232b2b0c5106c40,0xb8c510692c379881,0x4224c0e06202])))))) 22 (i % 16)
def s31Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x3c080100201f00,0x8628046200400c81,0x4315024960318801,0xc310010c9c0863e0,0x7a4b0092581800e0,0x61c0]) else (cbits [0xc78480120293302,0x8654243141419409,0x200f014960918804,0xc0098080d0640503,0xea4b0746283a0281,0x4998])) else (if j < 3 then (cbits [0x188070628380291c,0x18703892c1c3190e,0x201d0101a13b0fc7,0xc31014a4b0a86285,0x4b0f8b8c4e5292c2,0x4961]) else (cbits [0x80a0c926652c3830,0x1870689323400f80,0x20270101a1bb0fcd,0x93101d0c50e80387,0xf8100e40507201e3,0x18a1]))) else (if j < 6 then (if j < 5 then (cbits [0xa4b0e4c40726203f,0x18788a3144401580,0x2c3c4461e2398811,0x461f2230e12466e9,0x7003d3862802f444,0x13a]) else (cbits [0xa4b139258a26204e,0x92669c92d4e61c29,0x23150149ba731015,0x161c2c98d964064b,0xb0e175264ba31f0,0x1938])) else (if j < 7 then (cbits [0xbd1181870c001160,0x1278ca3436419580,0x8c3e6449f3218819,0xc49635988005e88c,0x7a4cdad25ad6c386,0x6203]) else (if j < 8 then (cbits [0x30f9c8c56029376b,0x403eea92c017a239,0xac387501bba80add,0xb00f3da4b405872e,0xf00a5f926602c3e7,0x194b]) else (cbits [0xa4b1f98990232b7e,0x126e02c407e62041]))))) 21 (i % 16)
def s31Links := pageLinks s31Index s31Codes 5 13 8 6
def s31Data (i : Nat) : Nat × Nat :=
  let e := s31Forest i
  (e &&& 255, e >>> 8)
def s31Sample : Nat × Nat := (s31Blob252972, 96)
def s31Tags := dagTraceTags s31Mask 96 (dagTagBases s31StockWords s31Blob253541 s31Blob253726 96) 8 s31Data
def s31States := dagTrace s31Mask s31StockWords 8 s31Data
def s31MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)))]
def s31Moves := dagMoves s31MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Autos : DagMovesOK s31Mask s31Goal 64 s31Moves := dagMovesOfCheck (by decide +kernel)
def s31Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x400c0400c2401,0x400000000000,0x101000]) else (cbits [0x100400c2400c3d00,0x81ff6acc77fd0440,0x3])) else (if j < 3 then (cbits [0x200020000,0x20400207980000,0x40400000]) else (cbits [0x22550040000,0xc237d0000,0x148e64]))) else (if j < 6 then (if j < 5 then (cbits [0x4f40121000,0x400a000001280000,0x80214]) else (cbits [0x100001,0x99000010008d0000,0x3d400000])) else (if j < 7 then (cbits [0x4f40000080,0x481004000801]) else (if j < 8 then (cbits [0x121000006f400,0x17d000010000,0x560df4]) else 0x5f5280000000000)))) 10 (i % 16)
def s31Check := dagCheckNode s31Mask s31Goal s31Chart (fun i => dagKnownCloses s31Goal (cutPick s31Cuts (s31Choice i))) 134 s31States s31Moves s31Links s31Sample s31Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Roots : dagCheckRoots s31Mask s31Goal s31Chart (dagKnownCloses s31Goal s31Cuts) s31Witnesses (dagRef 134 s31States s31Moves s31Links 0) s31StockWords 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Block0 : treeBlock 0 24 s31Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Block24 : treeBlock 24 24 s31Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Block48 : treeBlock 48 24 s31Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Block72 : treeBlock 72 24 s31Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Block96 : treeBlock 96 24 s31Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Block120 : treeBlock 120 14 s31Check = true := by decide +kernel
theorem s31Group24_48 : treeBlock 24 48 s31Check = true := treeBlock_merge (start := 24) (left := 24) (right := 24) (check := s31Check) s31Block24 s31Block48
theorem s31Group0_72 : treeBlock 0 72 s31Check = true := treeBlock_merge (start := 0) (left := 24) (right := 48) (check := s31Check) s31Block0 s31Group24_48
theorem s31Group96_38 : treeBlock 96 38 s31Check = true := treeBlock_merge (start := 96) (left := 24) (right := 14) (check := s31Check) s31Block96 s31Block120
theorem s31Group72_62 : treeBlock 72 62 s31Check = true := treeBlock_merge (start := 72) (left := 24) (right := 38) (check := s31Check) s31Block72 s31Group96_38
theorem s31Group0_134 : treeBlock 0 134 s31Check = true := treeBlock_merge (start := 0) (left := 72) (right := 62) (check := s31Check) s31Group0_72 s31Group72_62
theorem s31Blocks : treeBlock 0 134 s31Check = true := s31Group0_134
theorem s31Known : Known s31Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s30Stock) s13Stock) s6Stock) s29Stock) s28Stock) s27Stock) s21Stock) s26Stock) s25Stock) s24Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s31Stock : Lower s31Mask s31StockWords s31Goal 9 := by
  apply lowerDag s31Choice _ _ _ _ s31Autos _ _ _ s31Known _ s31Roots s31Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s31Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s32Mask : Nat := 0xa500a500a500a500
abbrev s32Goal : Nat := sGoal &&& s32Mask
abbrev s32StockWords : List Nat := [0xa000a000a000a000,0x8400840084008400,0xa5000000a5000000,0xa500a50000000000]
def s32Fact : Nat × List Nat × Nat × Nat := (s32Mask, s32StockWords, 6, s32Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s32Stock : Lower s32Mask s32StockWords s32Goal 6 := dagShiftLower (width := 64) pm0 s25Stock (by decide +kernel)
def s33Mask : Nat := 0xa5a5a5a5a5a5a5a5
abbrev s33Goal : Nat := sGoal &&& s33Mask
abbrev s33StockWords : List Nat := [0xa0a0a0a0a0a0a0a0,0x8484848484848484,0xa500a500a500a500,0xa5a50000a5a50000,0xa5a5a5a500000000]
def s33Fact : Nat × List Nat × Nat × Nat := (s33Mask, s33StockWords, 7, s33Goal)
def s33Witnesses := unpackWitnesses s33StockWords [3586, 265733, 554034, 797189, 1067525]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s33Stock : Lower s33Mask s33StockWords s33Goal 7 := by
  apply essentialLift (witnesses := s33Witnesses) (cut := s32Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s32StockWords) (by decide +kernel)
  · exact s32Stock
  · decide +kernel
def s34Blob270667 : Nat := (cbits [0x380c0e0301c0a07,0x40a150683c180e05,0x81d068742c170a05,0x50e078341e0b0783,0x68b44c27120940a2,0xb8542e130b8582d0,0x4c360b0d86835160,0x3a0d0e86836190d8,0xe0f0703a190e854,0x1c703c1a0f0583c,0xc2c070681c080701,0xe02038040e1301,0xe0d0382c0e068381,0x6038540e13038380,0x3c140f0303c0a0f1,0x2015068540815060,0x171a05438150b054,0xa05c24170305c0a,0x74281d060740a1d,0x8181e050780c1e0c,0xa1f0c078281e0907,0x50e07c341f0b07c1,0x3094402506894082,0x9c0a271a09458251,0xa2d1209c4427030,0x2e140b4482d060b4,0x110b8182e050b80c])
def s34Blob271235 : Nat := (cbits [0xfffc00f80047c7e3,0x7fb9393f0ffffc0f,0xf0f03ff0f03ffff8,0xffffffff87ffffff,0xf83e3e3cffffffff,0xff003fff003fff07,0xffc00007ffc03fc0,0xffffc00000003fff,0xffffc00000000007])
def s34Blob271451 : Nat := (cbits [0x1084082000024261,0x3b99190e01108401,0xb06218b06219b1c8,0xbeeedaf385efeff7,0xd836363857beed57,0x6a04b66a04b36c25,0xcf007046eec03d80,0x777d800000083b8c,0x8ccf000008038087])
def s34Mask : Nat := 0xf5f5f5f5f5f5f5f5
abbrev s34Goal : Nat := sGoal &&& s34Mask
abbrev s34StockWords : List Nat := [0xa0a0a0a0a0a0a0a0,0xc4c4c4c4c4c4c4c4,0xf0f0f0f0f0f0f0f0,0xf500f500f500f500,0xf5f50000f5f50000,0xf5f5f5f500000000]
def s34Fact : Nat × List Nat × Nat × Nat := (s34Mask, s34StockWords, 11, s34Goal)
def s34Cuts : List (Nat × List Nat × Nat × Nat) := [s31Fact, s17Fact, s19Fact, s16Fact, s20Fact, s33Fact, s24Fact, s32Fact, s26Fact, s8Fact, s22Fact, s27Fact]
def s34Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 14, 21, 37, 54, 58, 60, 7, 14, 21, 37, 54, 13, 22, 26, 28, 38, 42, 44, 50, 52, 56, 13, 22], rfl⟩
def s34Witnesses := unpackWitnesses s34StockWords [3590, 265733, 531466, 793606, 1059333, 1329669]
def s34Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 10 then (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x60609180188001,0xa006c40d801b0036,0x3e107820e841d003,0x88210082000]) else (cbits [0xd801a082c40469,0x200e401c8036186c,0x7630ec01c8839007,0xf801f003e00])) else (if j < 3 then (cbits [0x10d0208841007c3,0x6012c025804b0096,0x96312c025804b009,0x140627084e00]) else (if j < 4 then (cbits [0x116002a8c5310a60,0x8716c22c885900b0,0xce0198233006318b,0x1a82338c6700]) else (cbits [0x1d463a046c40d61,0xa01e863c087800f0,0x8320843e947d00f,0x224843888701])))) else (if j < 7 then (if j < 6 then (cbits [0x1244a48048e111a1,0xa326d44c0c97092c,0x5022a005400a8014,0x2bc25590aa09]) else (cbits [0x22cc25980b209602,0x432dc65b04b60168,0x9a233406604bd797,0x360067a4cf01])) else (if j < 8 then (cbits [0x36086c00d801b00,0x8b37006e00dc01b8,0xce139c07380e701b,0x3a0e7400e801]) else (if j < 9 then (cbits [0x73c407788ef01de0,0xe03f827c94f809e2,0x26044827fccff01f,0x46408c811332]) else (cbits [0x47008e01191a320,0xc0498091111c3238,0x5c44a0c9385260a4,0x4c8099013202]))))) else (if j < 15 then (if j < 12 then (if j < 11 then (cbits [0x14d0699853302641,0xb4e009c0138026e,0x86150c0a18143027,0x5300a29d440a]) else (cbits [0x158ccac2d4e52982,0xc05b80b5116a02d2,0xe605bc8b7056e02d,0x5d08ba01730a])) else (if j < 13 then (cbits [0x65f02bc117802f00,0x216202c3858322fa,0x2226402c6118a131,0x6524ca01930b]) else (if j < 14 then (cbits [0x6d4ad3b9a7034c1,0xa56f40dd0dba0374,0x8c07088e101c2037,0x7300e319c603]) else (cbits [0x73cce781cd13981,0xc17580eb01d50baa,0xc4a7804ef85d743a,0x7bc0f781ec1b])))) else (if j < 17 then (if j < 16 then (cbits [0x7d40f989ef23de0,0xe27dc0fb05f50bea,0xf617ec0fd81f913e,0x80010001fc23]) else (cbits [0x2815b00920104001,0x4085c70b82141c24,0x42488030d1a1a043,0x89811302250c])) else (if j < 18 then (cbits [0x8d851b0234144ce,0xa58f411e82382c70,0x8e091c1228a421c7,0x920523864704]) else (if j < 19 then (cbits [0x19a052cbe5334949,0xc19b0536026b0cd4,0xe639cc1388a6f14d,0x9e013b86760c]) else (cbits [0x29f013d867a0cf02,0x42a0433f8a7e0cf8,0xa1c1428a840d0])))))) 15 (i % 16)
def s34Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 20 then (if j < 10 then (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x7804c0100400003f,0x18a0ac02b0dc0520,0x2b2c064e448c5468,0x9758cfceb19999c3,0x17499a1e92d40925,0x47d8718ba4fd]) else (cbits [0x10c531f7a2242c3f,0x19581232701862a0,0x2b03925a06a4b00a,0x402a4b4044960060,0x7310010c3801cc6,0x30c400598c0])) else (if j < 3 then (cbits [0x2988008310808620,0x18a0440360400680,0x330b8c40168ccc2b,0x21ab0e03131b0606,0x140130220080d987,0x646280c009c]) else (if j < 4 then (cbits [0xfa4b01e193836326,0x49602432608525a0,0x2c0586280a802013,0xd24b01619302e9,0x1d49603831404801,0x4c628100044]) else (cbits [0xe98c017198034620,0x1904802508c0100,0x3109c64a130c5025,0x81530e0294960503,0x2c61c04633604466,0x90080140040])))) else (if j < 7 then (if j < 6 then (cbits [0x7b0e02619b032334,0x31804e0400a00381,0x388cd89019b0f032,0x17a4b02c310068c,0x3818a0200120a468,0x10064e1e8c54]) else (cbits [0xaa4b45249609c32b,0x49687492c0e40562,0x320446381d80743c,0x90c703f61c07c6,0x4100903601004cc5,0x6003c0a0070])) else (if j < 8 then (cbits [0x498d03e31008a314,0x3120843341358702,0x1c9112782224c043,0x2398904631a02a3,0x4200949093c12126,0x128c48230c50]) else (if j < 9 then (cbits [0x1804a4b49e096930,0x18a08801211c6282,0x280746382624b048,0x82798c04919202e3,0x4a1924a0c4814187,0x145870258c90]) else (cbits [0xa007c53008898630,0x31087462007c63c2,0x1e0806381d98803f,0x42698c43c3100423,0x5b18a8ae31408802,0x17c6522e8c94]))))) else (if j < 15 then (if j < 12 then (if j < 11 then (cbits [0x88cd4651998c6331,0x148cec381992581,0x1c1698702ca4b058,0x90c705c3180463,0x5c31004801e06c02,0x746382f30e0]) else (cbits [0x9890623180c0324,0x61c0c06341846483,0x200a463c12807064,0x150c78643188b26,0x690098bc631168c4,0x1b405635809c])) else (if j < 13 then (cbits [0x10c527201f8e4033,0x4960ae32b0e06520,0x3f2052663f24b477,0x842b0fc8361c5029,0x6c7a20d4c38a0de8,0xc629364940]) else (if j < 14 then (cbits [0x7a4f86e4960b0329,0x6250e0c3e9bd2943,0x369c64a038bd1270,0x3abd287461c0e60,0x7900f0f000f1da4a,0x9e807e3d00cc]) else (cbits [0xa0cfc741998d431f,0x61f8f6c38010c413,0x3e1f1e893dbd107d,0x370cd67f0250fe0,0x807a20b2635014c4,0x1bc06b404940])))) else (if j < 17 then (if j < 16 then (cbits [0x88cdc6c199905250,0x61c8f6c389d867e3,0x44211e894130fc80,0x93a81247501e8f8f,0x8861c10c9351f525,0x2280244398f0]) else (cbits [0x801289001f118036,0x19a85631d0186294,0x36250c642d8cdc3d,0x1511928a231f1346,0xac61f956c3929d87,0x2b5e8956312c])) else (if j < 18 then (cbits [0x5b0e2ad92815ef4b,0x61f51a94a23527c4,0x5023de894731288e,0x493d289161c51f2,0x9518e00e31424e4a,0x17066a4c0c74]) else (if j < 19 then (cbits [0xb0c5299928132f44,0x7a212ec380486524,0x3025cc50090cd297,0x45030f89f4961366,0xa1928142f44a8189,0x2752584e1882]) else (cbits [0xea4c29e7a213cc38,0x61c1466362792784,0x1e290c60534940a5,0xc458c78a90129500,0x831052234a24467,0x29527c1618a4])))))) else (if j < 30 then (if j < 25 then (if j < 22 then (if j < 21 then (cbits [0x54940aa7a254a94a,0x1a111a04027d2815,0x4226527d498d288f,0x553d12a64a51429,0x9202a1240482ba4a,0x2c4020048022]) else (cbits [0xe80d42d00f982011,0x7a2186635250c402,0x8b264a065bd2cc9,0x85900a42800992a0,0x1b1949783152e862,0xaf467e5e8ccc])) else (if j < 23 then (cbits [0xf3d10c061f97cc38,0x49916a6242cc6295,0x442e58715c24f8b8,0x5a0c50b4312572f,0xb761c16e92c2d8c4,0x2586285ba4c2]) else (if j < 24 then (cbits [0xdbd10bb61c166329,0x19a92e314070c695,0x122fde885d9880b9,0x4c0c501b01a0500,0xb2008038334308c4,0x31d87c6224c0]) else (cbits [0x44940c87a258ec4a,0x61c18a92c2d40216,0x1c2d8639633d10c6,0x85c8c70b800816e3,0x9949617c31c31987,0x32a4a0642504])))) else (if j < 27 then (if j < 26 then (cbits [0x60d00c000817e628,0x14814008334c786,0x252686281880d45f,0x1678d2ccf19f9863,0xdd4961b4632344c6,0x38987c7030e0]) else (cbits [0x3b12ee26251cec3f,0x9281d4f4b3a1e897,0x1d02c0106824f2e8,0xa4d8c50620148640,0xd019f9a033331064,0x350c66691882])) else (if j < 28 then (cbits [0xbb0e0d54965a863f,0x18a5aef4436587e6,0x38314c4a4e18800c,0x4e9882d37a21a6c,0x9e3105acf4435987,0x34d2586318c4]) else (if j < 29 then (cbits [0xdb0f8d87a21acc38,0x9281b8f44b6d8946,0x3e3552604f9882dc,0x6fbd12de6251bcc,0xe17a21acc3cb7e4a,0x28062970c940]) else (cbits [0x1b0e0de49618e325,0x1a1cd2503918947,0x31284c406d98f0e5,0x6e24f8d749e1906,0xe67a51c2f4437d87,0x36189074c942]))))) else (if j < 35 then (if j < 32 then (if j < 31 then (cbits [0x60c50e461e1b2630,0x1a51ea3373c066c7,0x3833cc6e511880f7,0x7fb12cfe61c9f8c,0xee61c1da04a4064a,0x28c62877c940]) else (cbits [0xa4940f36251e2630,0x49e1e4f442906287,0x383e00207b24f0f2,0x87d24b0f918a1f6c,0xfb3251dc6203e863,0x3f64a052a4b0])) else (if j < 33 then (cbits [0xa1908ef310200334,0x91faf442992587,0x3f41806682006d03,0x1a8c7c0d18a60c0,0xfc31994e6211dcc4,0x4258717e18fc]) else (if j < 34 then (cbits [0xc9883097a2216c3f,0x7a215292c2a0c423,0x2c41c05582c94105,0xe828c9d089280f49,0xaa4968f692cc2067,0x429e897ea4fc]) else (cbits [0xd98c47d3100f8c38,0x49e21cc38430c6a7,0x4a44807c8800690d,0xa1b0c7c0e18a6240,0xab3108fc62019866,0x3f8c7e6e98d4])))) else (if j < 38 then (if j < 36 then (cbits [0xb3d2d147a25fc64b,0x928222f44c524a08,0x2644e4a03f988311,0x24024b3131a52223,0x8118a22b25037d28,0x460652560c54]) else (if j < 37 then (cbits [0xc98c11e9285fe34b,0x31023b2504718948,0x2046d2788dbd111a,0x24198811d31a9046,0xe831b9926332b4c4,0x4258718098fc]) else (cbits [0x3d131e61fa28c39,0x49f95c92d2112589,0x45429e8874a50cca,0xe578c548518a22af,0xf71989d432b32c64,0x4a066a910ccc]))) else (if j < 39 then (cbits [0xb24b50b496256337,0x49ba6a9354bd2668,0x104e98729cb0e137,0x9200d1263202460,0x2731e24801049466,0x4a4c78928041]) else (if j < 40 then (cbits [0x6a4b12a31021892c,0x4a42586484986608,0x284b8050938cc12d,0x9898d1336202600,0x3431e2620284c866,0x2186289900a1]) else (cbits [0xc19208718a26c63c,0x3102689304cd2609,0x8730e088]))))))) 23 (i % 16)
def s34Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 10 then (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x6280200400407e00,0x9680d2580301580c,0x700731901c62a024,0x802c656021938098,0xa02496008c400c31,0x980525]) else (cbits [0x64c1200404406810,0x405404c11496048,0x4e11496054628150,0x30452581a18a0440,0xe114960706281c19,0x49604464])) else (if j < 3 then (cbits [0x6c1049684402220,0x1908c04a2300408c,0x622319288c628230,0xa0418702349608c6,0x101998418702c18,0x61c0bcc4]) else (if j < 4 then (cbits [0xc603231b040c6610,0x1c0418703461e0c8,0x2838014805872106,0xe8ed258390158e46,0x43e18a8e125a3900,0x61c0f8c6]) else (cbits [0x6684200910464e38,0x8a1052604331210c,0x604731211cc68461,0x8128c484a31a1052,0x63861c1052584c49,0x31813c65])))) else (if j < 7 then (if j < 6 then (cbits [0x2583861c1458784f,0x968e003e5300894d,0x525818a15c056014,0xa95d870584961600,0x5e19295cc605c18,0x19495d87]) else (cbits [0xc606031218464860,0x9995d8706419895c,0x280161c15d258571,0x39a58706a0099a46,0x86e0159a5e886c01,0x49f1b925])) else (if j < 8 then (cbits [0x66697a21b987c6e,0xa51cd8707301b1cc,0x1e784961a64a0737,0xc1e00667800f1e00,0xa6961f9e1e887c61,0x1f1fd25]) else (if j < 9 then (cbits [0x4a0824999a5e887f,0x1f9a5e888461c1a6,0x708631e21d26a866,0xc22c0248a18a8058,0xc8d49f23406c8a61,0x7a223587]) else (cbits [0xe949161c24407c8a,0x8e254c648a928245,0x3a9561c258628961,0x826cc6c8a7a22546,0x9c496270c409c31,0x49626d87]))))) else (if j < 15 then (if j < 12 then (if j < 11 then (cbits [0xc7c8a7a226d87c9b,0x1c28cc60a431b28c,0x3ca861c22a4a0a36,0xca29e88a8012aa00,0xae7a222987e8a61,0x7a5a2a4a]) else (cbits [0x52b20082c464e01,0x122ccc48b418a2cc,0x64b34962d8c40b63,0xc2ec628b261c2cd2,0xb2199ac862ab261,0x7a22fd87])) else (if j < 13 then (cbits [0xc40c2008ac587eb2,0x96315260c431aac4,0x88c461f311870c54,0x5ac64a0ca7a22c5e,0x60131e334680cc7a,0x19fb3c65]) else (if j < 14 then (cbits [0xc40d231833d278d0,0x96348c66d261c34c,0x88d861c349870d64,0xf36cc64cf61fb49e,0xcde49633de88db61,0x7a237987]) else (cbits [0x87ccf7a2385870cf,0x1a395894e361c38d,0x88cf61fb3e4a0e30,0x9805e96cf9283a5e,0xed0253b4628ec19,0x9283b587])))) else (if j < 17 then (if j < 16 then (cbits [0xe88f23183c466cec,0x9bbb24a0f16253c5,0x20f81a53b1278f61,0xc3e1258f918a3e40,0x2ec9283f5870ec61,0x625bb187]) else (cbits [0x258019283b066900,0xa24140370300940d,0xa10701541c067037,0xfc0de890a61c40e4,0x10c49e434c6b0c61,0x49680587])) else (if j < 18 then (cbits [0x7d107a244403510,0x28455e891092844c,0x5318499805e97109,0x2468c411a3184646,0x118928465895197a,0x61c0064a]) else (if j < 19 then (cbits [0x6672261f805e8920,0x984940692400848c,0x6b2231e49cc81231,0xbc88c412a31e4a46,0x12e4a44b0c912c19,0x499c8805]) else (cbits [0x6613231a4c405130,0x9ac88c79346204c0,0x913849bc88c79364,0x18732261c488c])))))) 22 (i % 16)
def s34Links := pageLinks s34Index s34Codes 5 13 9 6
def s34Data (i : Nat) : Nat × Nat :=
  let e := s34Forest i
  (e &&& 511, e >>> 9)
def s34Sample : Nat × Nat := (s34Blob270667, 96)
def s34Tags := dagTraceTags s34Mask 96 (dagTagBases s34StockWords s34Blob271235 s34Blob271451 96) 10 s34Data
def s34Num (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0xf5f5f5f5,0xf5f50000f5f5,0xf5f5f5f5f5f5,0x11f5f50011f5f5,0x31003100310031,0x31f5f50031f5f5,0x55005500550055,0xc400c400c400c4,0xf5000000f50000,0xf500f500f500f5,0x505353535353535,0x535053505350535,0x535353505353535,0x1111111111111111,0x1111555555555555,0x1155115511551155]) else (cbits [0x3100310031003100,0x3131000031310000,0x3131313131313131,0x3131f5f500000000,0x3131f5f53131f5f5,0x3175317531753175,0x5555555555555555,0xa0a0a0a0a0a0a0a0,0xa0f5a0f5a0f5a0f5,0xb1b1b1b1b1b1b1b1,0xc400c400c400c400,0xc480c480c480c480,0xc4c4000000000000,0xc4c40000c4c40000,0xc4c4c4c4c4c4c4c4,0xc4d5c4d5c4d5c4d5])) else (if j < 3 then (cbits [0xc4f5c4c4c4f5c4c4,0xe400e400e400e400,0xe4a00000e4a00000,0xe4a0e4a0e4a0e4a0,0xe4e4a0a0a0a0a0a0,0xe4e4e4e4e4e4e4e4,0xf0c00000f0c00000,0xf0c0c0c0f0c0c0c0,0xf0c0f000f0c0f000,0xf0c0f0c0f0c0f0c0,0xf0e0f0e0f0e0f0e0,0xf0f0c000c000c000,0xf0f0c0c0c0c0c0c0,0xf0f0f000f000f000,0xf0f0f0f0f0f0f0f0,0xf500000000000000]) else (if j < 4 then (cbits [0xf5000000f5000000,0xf500c400c400c400,0xf500f50000000000,0xf500f500f500f500,0xf5310000f5310000,0xf531f500f531f500,0xf531f531f531f531,0xf5a0a0a0a0a0a0a0,0xf5a0e4a0e4a0e4a0,0xf5a0f5a0f5a0f5a0,0xf5b1f5b1f5b1f5b1,0xf5c4000000000000,0xf5c40000f5c40000,0xf5c4c4c400000000,0xf5c4c4c4f5c4c4c4,0xf5c4f50000000000]) else (cbits [0xf5c4f500c4c40000,0xf5c4f500f5c4f500,0xf5c4f5c4f5c4f5c4,0xf5e40000f5e40000,0xf5e4a0a0a0a0a0a0,0xf5e4f5e4f5e4f5e4,0xf5f5000000000000,0xf5f50000f5f50000,0xf5f5c400c400c400,0xf5f5c4c4c4c4c4c4,0xf5f5f500f500f500,0xf5f5f5f500000000])))) 64 (i % 16)
def s34Entry (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 10 then (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x5fe90000003fa,0xe4fc70002e4fc800,0xbc7017262b470372,0x70002e4fe8017262,0x17262b6701b2e4fc,0x865fe8000365fe80,0x33a6000545fa7000,0xe80002e2b680002e,0x9bf90002e2b]) else (cbits [0xa4c4f47000749b68,0x61f4603a484f4603,0xb4603a4c73470262,0x603a383b4603a4c5,0x3a4c7367026381f4,0x1c1f66000743b670,0x4366000749367000,0x67000481f6600074,0x4c1f6703a4c93])) else (if j < 3 then (cbits [0xa4c1f67026401f46,0xc4fc7000749be803,0x3c703a4c6f6703a4,0x7000743be703a4c7,0x4c93e703a4c8b6,0x4c1fe703a4c2b670,0x2b570004c4fd8000,0xf80004c6ff802626,0x1c2b77000003b]) else (if j < 4 then (cbits [0x11bf80004c8bf8,0x112f700000afb700,0xb780000012f60000,0x90004c2bf80004c2,0x744f5800000eb7,0x261f5703b744f570,0x1f57019261f46000,0x57000744f7803a26,0x261f7703a384f]) else (cbits [0xa487367000747378,0x8730504648734603,0xb7704448724502b4,0x50008c5b56000745,0x885a55000565b1,0x5673160008c73570,0x1255000887256000,0x78000381f7700038,0x74af370008ceb])))) else (if j < 7 then (if j < 6 then (cbits [0x74127600088ea77,0x21f67000001f7800,0xf78000401f770003,0x800000ebf9000741,0x3a6e4f57000744fd,0x261fd703a262b570,0x4f57000744ff8000,0x77000746f7803a36,0x86eb78000361f]) else (cbits [0x547316000867357,0x73f800074ab3700,0x3f8000382b770000,0x8000742b78000747,0x4fd9000001ff,0x262b57000344fd80,0xad70002647d801a,0x570006e4fd801322,0x37624f57037262b])) else (if j < 8 then (cbits [0x7260ad70006a4fd7,0xc4fd7000264bd803,0xad7013242b570006,0x80132405d7047264,0x13141757000262b5,0x142757000324f570,0x456013140a57013,0xd8047262b5798a04,0x2627d7000262b]) else (if j < 9 then (cbits [0x624fd8013140ad7,0x60ad80312605d700,0xfd80130404d70002,0x6000964fd70008e4,0x260fd70005c4f9,0x6bf8000004ff90,0xdff8000342b77000,0xf70006ec77700000,0x6e0af700000d7]) else (cbits [0x242b77000004bf8,0x405f70008e4af700,0xfc7000364fd80002,0x60002643c6000484,0x484fd7024260ac,0x864fd801b260ad70,0x3396000544f97000,0x9602a262b1600026,0x43262b5702a260a]))))) else (if j < 15 then (if j < 12 then (if j < 11 then (cbits [0x3260ad70007a4fd7,0x44fd70003c4fd804,0xb57000524f960008,0x801e2605d701e262,0x324f77000262b7,0x140a770131423570,0x4ff8000262bf8013,0xf7000260af800062,0x8e4ff80130404]) else (cbits [0x93e8000006ff9,0x6436600086936700,0x3260005443250008,0x5000483325000549,0x7a936602a480a2,0x43e7043480a660,0x43e7000200ae6000,0xe7000488fe700048,0x240404e6000480a])) else (if j < 13 then (cbits [0x93f80008e93e7,0x66f780000043f700,0x336000546f370008,0x702a360a36000363,0x43360a770007a6f7,0x404f7000360af80,0x27f70008e6ff801b,0xf900000b3b600001,0x867bf8000010f]) else (if j < 14 then (cbits [0xabb8000547bb7,0x80ab60000033b700,0xb37000549fb70001,0x702a140a36000542,0x2a0404b6000540ab,0x86abb80008eabb70,0xab70007aabb7000,0x77000862b7804354,0x43140a770007a2b]) else (cbits [0xa0af70000017f8,0x1bf700000f7f800,0x7e600000f3f70000,0x80007a05f7000011,0x860af800086f7f,0x8f0ff80430404f70,0x57f8000007bf9000,0x770000053f700000,0x2a05f70002a2b])))) else (if j < 17 then (if j < 16 then (cbits [0xa7b7000010bf8,0x103f70005205b600,0xbf80008405f70000,0x8000527bb7000847,0x97e70000077f,0x4a2b66000003fe60,0x2b780003a2b77000,0xf801e1405770003c,0x667bf80003c2b]) else (cbits [0x3c05f80000107f7,0x6778000002b7900,0xa770001423780000,0x700014277800a100,0xa120577000422b7,0x40477000140a780,0x2b770008e2b7800a,0x770005a2b3600094,0x2bf9000140f])) else (if j < 18 then (cbits [0x100af70000023f8,0x205f70000027f800,0x4f7000140af80001,0x90008e2bf800a040,0xfff800000c7f,0x37b600000a3b70,0xfbf70005005b6000,0xf80007e05f700000,0xaf90006205]) else (if j < 19 then (cbits [0x11ff90000404f8,0xe97e70008e77f800,0x7850009497c60008,0x60009477d70005a9,0x12bf80005a779,0x2fb600000b7b70,0xb7b7000951ff8000,0x660008ecb770008e,0x8ec3f80008ee7]) else (cbits [0x96e3660008ee3e7,0x6c37700070bb2500,0xff800060bb360009,0x800000bbb7000012,0x8ebbb7000971ff,0x8e0ff8000000ff80])))))) 36 (i % 16)
def s34Ids (i : Nat) := materialize [23, 30, 46, 51, 71, 75] 7 127 4 (s34Entry i >>> 4)
def s34Words (i : Nat) := (s34Ids i).map s34Num
def s34States (i : Nat) : Option (Nat × List Nat × List (Nat × Nat × Nat)) := some (s34Entry i &&& 15, s34Words i, shortHist s34Mask 10 s34Words s34Data i)
def s34MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)))]
def s34Moves := dagMoves s34MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Autos : DagMovesOK s34Mask s34Goal 64 s34Moves := dagMovesOfCheck (by decide +kernel)
def s34Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 10 then (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x1b00021b01b01b,0x5b25b00000265b00,0x25b45b45b00065b6]) else (cbits [0x1900000021b219,0x5b00000000000,0x592020000002190])) else (if j < 3 then (cbits [0x40359240000,0x4020100004000,0x2db20000035b0]) else (if j < 4 then (cbits [0xb000293a9a29b200,0x1b00021b01b0c20d,0x200029b0400000]) else (cbits [0x200000000000229b,0x1a09b00000000000,0xa9a29b0000000138])))) else (if j < 7 then (if j < 6 then (cbits [0xb04005b09b000293,0x4000231b0db2d,0x39b00025b0003c20]) else (cbits [0x20401dbb9a91a19b,0x15b01b2db0db0c,0x15b00035b0])) else (if j < 8 then (cbits [0x400000025b000000,0x1b00105b00000,0x25b0080000090]) else (if j < 9 then (cbits [0xb00901b00015b000,0xdb35b00800000035,0x4db0001]) else (cbits [0x115b0000040003cf,0x5b00000200000004,0x3413]))))) else (if j < 15 then (if j < 12 then (if j < 11 then (cbits [0x15b000000,0xdb00000,0x31800005b3401c00]) else (cbits [0x31915915b,0x4100000800000010,0x490020400000])) else (if j < 13 then (cbits [0x35b35b00025b048,0x5b00000800000,0x2db0000400580]) else (if j < 14 then (cbits [0x1000000861adb000,0xda008000049000cc,0x4db000000a]) else (cbits [0x800800000f0012db,0x8800005b00800000,0x1cf15b0])))) else (if j < 17 then (if j < 16 then (cbits [0x98819b,0x1191db10010,0x480c00000db0000]) else (cbits [0x4db05b05b05f000,0x905b00000809b00,0x5b0080000800db0])) else (if j < 18 then (cbits [0x5b0002cf0005db,0x4024825b05b0c800,0x1b05f0480000400]) else (if j < 19 then (cbits [0x800800805b01b,0x2182df00800800,0x80080080080080]) else (cbits [0xf008008000008008,0xc3df00800889819])))))) 12 (i % 16)
def s34Check := dagCheckNode s34Mask s34Goal s34Chart (fun i => dagKnownCloses s34Goal (cutPick s34Cuts (s34Choice i))) 315 s34States s34Moves s34Links s34Sample s34Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Roots : dagCheckRoots s34Mask s34Goal s34Chart (dagKnownCloses s34Goal s34Cuts) s34Witnesses (dagRef 315 s34States s34Moves s34Links 0) s34StockWords 10 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Block0 : treeBlock 0 24 s34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Block24 : treeBlock 24 24 s34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Block48 : treeBlock 48 24 s34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Block72 : treeBlock 72 24 s34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Block96 : treeBlock 96 24 s34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Block120 : treeBlock 120 24 s34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Block144 : treeBlock 144 24 s34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Block168 : treeBlock 168 24 s34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Block192 : treeBlock 192 24 s34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Block216 : treeBlock 216 24 s34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Block240 : treeBlock 240 24 s34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Block264 : treeBlock 264 24 s34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Block288 : treeBlock 288 24 s34Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Block312 : treeBlock 312 3 s34Check = true := by decide +kernel
theorem s34Group24_48 : treeBlock 24 48 s34Check = true := treeBlock_merge (start := 24) (left := 24) (right := 24) (check := s34Check) s34Block24 s34Block48
theorem s34Group0_72 : treeBlock 0 72 s34Check = true := treeBlock_merge (start := 0) (left := 24) (right := 48) (check := s34Check) s34Block0 s34Group24_48
theorem s34Group72_48 : treeBlock 72 48 s34Check = true := treeBlock_merge (start := 72) (left := 24) (right := 24) (check := s34Check) s34Block72 s34Block96
theorem s34Group120_48 : treeBlock 120 48 s34Check = true := treeBlock_merge (start := 120) (left := 24) (right := 24) (check := s34Check) s34Block120 s34Block144
theorem s34Group72_96 : treeBlock 72 96 s34Check = true := treeBlock_merge (start := 72) (left := 48) (right := 48) (check := s34Check) s34Group72_48 s34Group120_48
theorem s34Group0_168 : treeBlock 0 168 s34Check = true := treeBlock_merge (start := 0) (left := 72) (right := 96) (check := s34Check) s34Group0_72 s34Group72_96
theorem s34Group192_48 : treeBlock 192 48 s34Check = true := treeBlock_merge (start := 192) (left := 24) (right := 24) (check := s34Check) s34Block192 s34Block216
theorem s34Group168_72 : treeBlock 168 72 s34Check = true := treeBlock_merge (start := 168) (left := 24) (right := 48) (check := s34Check) s34Block168 s34Group192_48
theorem s34Group240_48 : treeBlock 240 48 s34Check = true := treeBlock_merge (start := 240) (left := 24) (right := 24) (check := s34Check) s34Block240 s34Block264
theorem s34Group288_27 : treeBlock 288 27 s34Check = true := treeBlock_merge (start := 288) (left := 24) (right := 3) (check := s34Check) s34Block288 s34Block312
theorem s34Group240_75 : treeBlock 240 75 s34Check = true := treeBlock_merge (start := 240) (left := 48) (right := 27) (check := s34Check) s34Group240_48 s34Group288_27
theorem s34Group168_147 : treeBlock 168 147 s34Check = true := treeBlock_merge (start := 168) (left := 72) (right := 75) (check := s34Check) s34Group168_72 s34Group240_75
theorem s34Group0_315 : treeBlock 0 315 s34Check = true := treeBlock_merge (start := 0) (left := 168) (right := 147) (check := s34Check) s34Group0_168 s34Group168_147
theorem s34Blocks : treeBlock 0 315 s34Check = true := s34Group0_315
theorem s34Known : Known s34Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s27Stock) s22Stock) s8Stock) s26Stock) s32Stock) s24Stock) s33Stock) s20Stock) s16Stock) s19Stock) s17Stock) s31Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s34Stock : Lower s34Mask s34StockWords s34Goal 11 := by
  apply lowerDag s34Choice _ _ _ _ s34Autos _ _ _ s34Known _ s34Roots s34Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s34Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s35Mask : Nat := 0xff55ff55ff55ff55
abbrev s35Goal : Nat := sGoal &&& s35Mask
abbrev s35StockWords : List Nat := [0xaa00aa00aa00aa00,0xcc44cc44cc44cc44,0xf050f050f050f050,0xff00ff00ff00ff00,0xff550000ff550000,0xff55ff5500000000]
def s35Fact : Nat × List Nat × Nat × Nat := (s35Mask, s35StockWords, 11, s35Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s35Stock : Lower s35Mask s35StockWords s35Goal 11 := dagShiftLower (width := 64) pm0 s34Stock (by decide +kernel)
def s36Mask : Nat := 0xffff
abbrev s36Goal : Nat := sGoal &&& s36Mask
abbrev s36StockWords : List Nat := [0xaaaa,0xcccc,0xf0f0,0xff00]
def s36Fact : Nat × List Nat × Nat × Nat := (s36Mask, s36StockWords, 5, s36Goal)
def s36Witnesses := unpackWitnesses s36StockWords [3590, 265733, 527875, 792067]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s36Stock : Lower s36Mask s36StockWords s36Goal 5 := by
  apply essentialLift (witnesses := s36Witnesses) (cut := s0Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s0StockWords) (by decide +kernel)
  · exact s0Stock
  · decide +kernel
def s37Blob282240 : Nat := (cbits [0x82c0c070281c0607,0x80c0e0502c120b01,0x2110683c180e0503,0x50904c0613080440,0x48642c170a0540a1,0x741a1d0d06c30190,0x381e0d0782c1e0e0,0x70201c04070081c,0x102c020b0b01c1a,0x38340b0682c100b,0x81a0e04038080e01,0x60f0e038340e0b03,0xf0483c0c0f0283c0,0x184400110603c140,0x442411048440a110,0x4130084c30110a0,0x150d04c2c130804c,0x80541a150205402,0x85c06170e0542c15,0x428170905c0c1702,0x190686410190086,0xb0186c38190d0642,0xc06c241b0506c121,0x74181d048740a1d0,0x141e03078301d0a0,0x1e0a078241e06078,0xd07c2c1f0687c30])
def s37Blob282809 : Nat := (cbits [0xfffffc07fe3ffe3f,0xffc933ffe07fffff,0xff83e07c0f80ffff,0xf000fff83ff1c3c7,0xc1fe03f8fffc007f,0xffffff800000ffff,0xffff000001fffc00,0xffffffff])
def s37Blob282997 : Nat := (cbits [0x508e2c425212561b,0xa4c930ed200c628c,0xc581a8350d12558c,0x64249ad23971c346,0x11be03b06ab4125b,0xb35adb024848e367,0x8e70038421eda800,0xdc631c63])
def s37Mask : Nat := 0xffffffff
abbrev s37Goal : Nat := sGoal &&& s37Mask
abbrev s37StockWords : List Nat := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
def s37Fact : Nat × List Nat × Nat × Nat := (s37Mask, s37StockWords, 7, s37Goal)
def s37Cuts : List (Nat × List Nat × Nat × Nat) := [s36Fact, s4Fact]
def s37Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 11, 14, 17, 7, 11, 14, 17, 7, 11, 14, 17, 3, 13, 22, 26, 28, 3, 13, 22, 26, 28, 3, 13], rfl⟩
def s37Witnesses := unpackWitnesses s37StockWords [3590, 265733, 527875, 792067, 1057281]
def s37Index (i : Nat) : Nat := unpack 0x840e1 5 i
def s37Codes (i : Nat) : Nat := unpack 0xc92c46202008001f 16 i
def s37Forest (i : Nat) : Nat := unpack 0x6204010807c 15 i
def s37Links := pageLinks s37Index s37Codes 2 13 2 3
def s37Data (i : Nat) : Nat × Nat :=
  let e := s37Forest i
  (e &&& 3, e >>> 2)
def s37Sample : Nat × Nat := (s37Blob282240, 96)
def s37Tags := dagTraceTags s37Mask 96 (dagTagBases s37StockWords s37Blob282809 s37Blob282997 96) 6 s37Data
def s37States := dagTrace s37Mask s37StockWords 6 s37Data
def s37MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)))]
def s37Moves := dagMoves s37MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Autos : DagMovesOK s37Mask s37Goal 64 s37Moves := dagMovesOfCheck (by decide +kernel)
def s37Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack 0x3 2 (i % 16)
def s37Check := dagCheckNode s37Mask s37Goal s37Chart (fun i => dagKnownCloses s37Goal (cutPick s37Cuts (s37Choice i))) 3 s37States s37Moves s37Links s37Sample s37Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Roots : dagCheckRoots s37Mask s37Goal s37Chart (dagKnownCloses s37Goal s37Cuts) s37Witnesses (dagRef 3 s37States s37Moves s37Links 0) s37StockWords 6 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Block0 : treeBlock 0 3 s37Check = true := by decide +kernel
theorem s37Blocks : treeBlock 0 3 s37Check = true := s37Block0
theorem s37Known : Known s37Cuts := (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s4Stock) s36Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s37Stock : Lower s37Mask s37StockWords s37Goal 7 := by
  apply lowerDag s37Choice _ _ _ _ s37Autos _ _ _ s37Known _ s37Roots s37Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s37Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl <;> decide +kernel
def s38Blob286878 : Nat := (cbits [0x82c0c070281c0607,0x80c0e0502c120b01,0x2110683c180e0503,0x50904c0613080440,0x48642c170a0540a1,0x741a1d0d06c30190,0x381e0d0782c1e0e0,0x36160b8542e130b8,0x1a0d86436130d82c,0xe8643a150e8343a,0x683c160f0383c1c,0x8070101c02071c0f,0xb1301c2c070681c0,0x682c100b0102c020,0x38040e1502c340b0,0x2c0e06838100e020,0xe13038380e0d038,0x283c060f1603854,0x3c140f0483c0c0f,0x40a1101844001106,0x110a04424110484,0x30104c0213180443,0x904c34130b04c201,0x541a150205402151,0x68150e0542c15080,0x170305c0a170185c,0x406402190a05c24])
def s38Blob287447 : Nat := (cbits [0xc00fff00003ffe3f,0xffc933ffffffffff,0x3e03f00fffffff0f,0xfff03ff0fff1c3c7,0xffe03f83ffc000f,0xc000000fffffc0ff,0xfff1fffc00,0xfe000000fffffff0,0xff])
def s38Blob287642 : Nat := (cbits [0xc08249000012561b,0x76c930ed461410e2,0x1a43a1255b1cb207,0xada23c70bb71c346,0xdbe03b02dd88249,0x8091048e36cf08bb,0x70410ddd1eda800,0xee00000031e3cf00,0x1020800380820ee])
def s38Mask : Nat := 0x55555555ffffffff
abbrev s38Goal : Nat := sGoal &&& s38Mask
abbrev s38StockWords : List Nat := [0xaaaaaaaa,0x44444444cccccccc,0x50505050f0f0f0f0,0x55005500ff00ff00,0x55550000ffff0000,0x5555555500000000]
def s38Fact : Nat × List Nat × Nat × Nat := (s38Mask, s38StockWords, 10, s38Goal)
def s38Cuts : List (Nat × List Nat × Nat × Nat) := [s17Fact, s16Fact, s20Fact, s37Fact, s4Fact, s21Fact, s22Fact]
def s38Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 11, 14, 17, 54, 58, 60, 7, 11, 14, 17, 54, 3, 13, 22, 26, 28, 38, 42, 44, 50, 52, 56, 3], rfl⟩
def s38Witnesses := unpackWitnesses s38StockWords [3590, 265733, 527875, 792067, 1057281, 1338390]
def s38Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0xb01512a03600e001,0x80610b89702c2580,0x4628c0e39c03]) else (if j < 2 then (cbits [0x302514a094120a40,0x50a81502a052298d,0x660c85903205]) else (cbits [0x84017e2de1b8334,0x651d2384708a5052,0x270cd19]))) 11 (i % 16)
def s38Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0xb12315023140003f,0x2b983272a31f1831,0x6273e62134620aa3,0xe92db492c5262b42,0x66208432b0431fb]) else (cbits [0xc1062b0c6270a621,0x340892c8a92d8692,0x632146260e6240e9,0xa31496c381692c94,0x20632146201c3321])) else (if j < 3 then (cbits [0x28c38269322492c,0x3022630229301e01,0x92c32c38309322c9,0x66203832b3631f2e,0xb262ba8627166210]) else (if j < 4 then (cbits [0x892c3c92d3a92c,0x3840932246250a62,0x3251c3190c314bcc,0x92c44620a633126,0x46934c0c384a9344]) else (cbits [0x54c3240e31448624,0x204e314466205032,0x3315433010314486,0xc624563144a62458,0x509304e6244])))) 20 (i % 16)
def s38Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x431f08628080fc0,0x2708c42124b04310,0x862a098ac249a0e6,0x868c6c1496146262,0x81e3323462]) else (if j < 2 then (cbits [0x1a92c35260898c8d,0x305863e0b0e0d499,0x5870b24c964962e9,0x8d8cadb18fb66200,0x3108292d6d25]) else (cbits [0x4662088c4e0a4ca0,0x249926911892449a,0x8c5608c96618a4e3,0xcc6a18a56330a]))) 19 (i % 16)
def s38Links := pageLinks s38Index s38Codes 4 13 6 5
def s38Data (i : Nat) : Nat × Nat :=
  let e := s38Forest i
  (e &&& 63, e >>> 6)
def s38Sample : Nat × Nat := (s38Blob286878, 96)
def s38Tags := dagTraceTags s38Mask 96 (dagTagBases s38StockWords s38Blob287447 s38Blob287642 96) 9 s38Data
def s38States := dagTrace s38Mask s38StockWords 9 s38Data
def s38MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)))]
def s38Moves := dagMoves s38MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Autos : DagMovesOK s38Mask s38Goal 64 s38Moves := dagMovesOfCheck (by decide +kernel)
def s38Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x9800000000e00b87,0x180770003b]) else (if j < 2 then (cbits [0xddf80a001020,0xee00380009e4]) else (cbits [0x80001d3800003b80,0x19ff]))) 7 (i % 16)
def s38Check := dagCheckNode s38Mask s38Goal s38Chart (fun i => dagKnownCloses s38Goal (cutPick s38Cuts (s38Choice i))) 45 s38States s38Moves s38Links s38Sample s38Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Roots : dagCheckRoots s38Mask s38Goal s38Chart (dagKnownCloses s38Goal s38Cuts) s38Witnesses (dagRef 45 s38States s38Moves s38Links 0) s38StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block0 : treeBlock 0 24 s38Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Block24 : treeBlock 24 21 s38Check = true := by decide +kernel
theorem s38Group0_45 : treeBlock 0 45 s38Check = true := treeBlock_merge (start := 0) (left := 24) (right := 21) (check := s38Check) s38Block0 s38Block24
theorem s38Blocks : treeBlock 0 45 s38Check = true := s38Group0_45
theorem s38Known : Known s38Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s22Stock) s21Stock) s4Stock) s37Stock) s20Stock) s16Stock) s17Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s38Stock : Lower s38Mask s38StockWords s38Goal 10 := by
  apply lowerDag s38Choice _ _ _ _ s38Autos _ _ _ s38Known _ s38Roots s38Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s38Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s39Mask : Nat := 0x5555ffff5555ffff
abbrev s39Goal : Nat := sGoal &&& s39Mask
abbrev s39StockWords : List Nat := [0xaaaa0000aaaa,0x4444cccc4444cccc,0x5050f0f05050f0f0,0x5500ff005500ff00,0x5555000055550000,0x5555ffff00000000]
def s39Fact : Nat × List Nat × Nat × Nat := (s39Mask, s39StockWords, 10, s39Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s39Stock : Lower s39Mask s39StockWords s39Goal 10 := dagShiftLower (width := 64) pm6 s38Stock (by decide +kernel)
def s40Mask : Nat := 0xff00ff00ff00ff
abbrev s40Goal : Nat := sGoal &&& s40Mask
abbrev s40StockWords : List Nat := [0xaa00aa00aa00aa,0xcc00cc00cc00cc,0xf000f000f000f0,0xff000000ff0000,0xff00ff00000000]
def s40Fact : Nat × List Nat × Nat × Nat := (s40Mask, s40StockWords, 7, s40Goal)
def s40Witnesses := unpackWitnesses s40StockWords [3590, 265733, 527875, 795137, 1065473]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s40Stock : Lower s40Mask s40StockWords s40Goal 7 := by
  apply essentialLift (witnesses := s40Witnesses) (cut := s2Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s2StockWords) (by decide +kernel)
  · exact s2Stock
  · decide +kernel
def s41Blob295211 : Nat := (cbits [0x380c070281c0607,0x4021106038140e03,0xa150904c06130804,0xe0b0782c170a0540,0x8402210e078341,0x940a251108c06231,0x542e130b84c27120,0x35190cc6031160b8,0x190d84c360b0d868,0xe8543a0d0e86836,0x583c0e0f0703a19,0x4070081c703c1a0f,0xe1301c2c070201c0,0xb038100e02038040,0x384c0e0e038340e0,0x61100044580e150,0x110a044241102844,0x104c02131804430,0x4c34130b04c2013,0x4201502054021519,0x6171a05438150b05,0x70905c0c170285c0,0x6078141e03078281,0x84301e0a078241e0,0x4421028840621000,0x2318084502112084,0x1308c40230108c02])
def s41Blob295779 : Nat := (cbits [0xff803e001c7f1fc7,0xebccf33fffe07fff,0xf01ffc0fc07ffe1f,0x7fffe1f3f0fc3f,0x380e038001ffff0,0x1f8000007fc1fe,0xff8001fffc00ffc0,0xffff0000001fffff,0xffe00000000001ff])
def s41Blob295990 : Nat := (cbits [0x4300020000150543,0xe9cc731d10c00c10,0xa145b48e8536740e,0xa5ab8e172f0bc2e,0x300c030828adba2,0x4130104106d0176,0x3c0e11bbbc00fa80,0xdfea0000081c63cf,0xcf000208207021dd])
def s41Mask : Nat := 0x55ff55ff55ff55ff
abbrev s41Goal : Nat := sGoal &&& s41Mask
abbrev s41StockWords : List Nat := [0xaa00aa00aa00aa,0x44cc44cc44cc44cc,0x50f050f050f050f0,0x5500550055005500,0x55ff000055ff0000,0x55ff55ff00000000]
def s41Fact : Nat × List Nat × Nat × Nat := (s41Mask, s41StockWords, 10, s41Goal)
def s41Cuts : List (Nat × List Nat × Nat × Nat) := [s17Fact, s16Fact, s20Fact, s40Fact, s2Fact, s24Fact, s22Fact]
def s41Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 14, 17, 33, 54, 58, 60, 7, 14, 17, 33, 54, 3, 5, 22, 26, 28, 38, 42, 44, 50, 52, 56, 3], rfl⟩
def s41Witnesses := unpackWitnesses s41StockWords [3590, 265733, 527875, 793606, 1057281, 1327617]
def s41Index (i : Nat) : Nat := unpack 0x48910603970c4681 7 i
def s41Codes (i : Nat) : Nat := unpack (cbits [0xc6c6314080a8003f,0x492c3a4b2662028,0xc3142188]) 18 i
def s41Forest (i : Nat) : Nat := unpack (cbits [0x8a0a4b08054203f0,0x608c518636262041,0x49]) 17 i
def s41Links := pageLinks s41Index s41Codes 3 13 4 4
def s41Data (i : Nat) : Nat × Nat :=
  let e := s41Forest i
  (e &&& 15, e >>> 4)
def s41Sample : Nat × Nat := (s41Blob295211, 96)
def s41Tags := dagTraceTags s41Mask 96 (dagTagBases s41StockWords s41Blob295779 s41Blob295990 96) 9 s41Data
def s41States := dagTrace s41Mask s41StockWords 9 s41Data
def s41MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm15, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)))]
def s41Moves := dagMoves s41MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Autos : DagMovesOK s41Mask s41Goal 64 s41Moves := dagMovesOfCheck (by decide +kernel)
def s41Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack 0x7e41f977edff3f 7 (i % 16)
def s41Check := dagCheckNode s41Mask s41Goal s41Chart (fun i => dagKnownCloses s41Goal (cutPick s41Cuts (s41Choice i))) 8 s41States s41Moves s41Links s41Sample s41Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Roots : dagCheckRoots s41Mask s41Goal s41Chart (dagKnownCloses s41Goal s41Cuts) s41Witnesses (dagRef 8 s41States s41Moves s41Links 0) s41StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Block0 : treeBlock 0 8 s41Check = true := by decide +kernel
theorem s41Blocks : treeBlock 0 8 s41Check = true := s41Block0
theorem s41Known : Known s41Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s22Stock) s24Stock) s2Stock) s40Stock) s20Stock) s16Stock) s17Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s41Stock : Lower s41Mask s41StockWords s41Goal 10 := by
  apply lowerDag s41Choice _ _ _ _ s41Autos _ _ _ s41Known _ s41Roots s41Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s41Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s42Mask : Nat := 0x5f5f5f5f5f5f5f5f
abbrev s42Goal : Nat := sGoal &&& s42Mask
abbrev s42StockWords : List Nat := [0xa0a0a0a0a0a0a0a,0x4c4c4c4c4c4c4c4c,0x5050505050505050,0x5f005f005f005f00,0x5f5f00005f5f0000,0x5f5f5f5f00000000]
def s42Fact : Nat × List Nat × Nat × Nat := (s42Mask, s42StockWords, 10, s42Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s42Stock : Lower s42Mask s42StockWords s42Goal 10 := dagShiftLower (width := 64) pm0 s41Stock (by decide +kernel)
def s43Mask : Nat := 0x3333333333333333
abbrev s43Goal : Nat := sGoal &&& s43Mask
abbrev s43StockWords : List Nat := [0x2222222222222222,0x3030303030303030,0x3300330033003300,0x3333000033330000,0x3333333300000000]
def s43Fact : Nat × List Nat × Nat × Nat := (s43Mask, s43StockWords, 6, s43Goal)
def s43Witnesses := unpackWitnesses s43StockWords [8720, 292920, 555060, 795137, 1065473]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s43Stock : Lower s43Mask s43StockWords s43Goal 6 := by
  apply essentialLift (witnesses := s43Witnesses) (cut := s6Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s6StockWords) (by decide +kernel)
  · exact s6Stock
  · decide +kernel
def s44Mask : Nat := 0x3003300330033003
abbrev s44Goal : Nat := sGoal &&& s44Mask
abbrev s44StockWords : List Nat := [0x2002200220022002,0x3000300030003000,0x3003000030030000,0x3003300300000000]
def s44Fact : Nat × List Nat × Nat × Nat := (s44Mask, s44StockWords, 5, s44Goal)
def s44Witnesses := unpackWitnesses s44StockWords [8720, 292912, 532993, 803329]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s44Stock : Lower s44Mask s44StockWords s44Goal 5 := by
  apply essentialLift (witnesses := s44Witnesses) (cut := s6Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s6StockWords) (by decide +kernel)
  · exact s6Stock
  · decide +kernel
def s45Mask : Nat := 0x3300330033003300
abbrev s45Goal : Nat := sGoal &&& s45Mask
abbrev s45StockWords : List Nat := [0x2200220022002200,0x3000300030003000,0x3300000033000000,0x3300330000000000]
def s45Fact : Nat × List Nat × Nat × Nat := (s45Mask, s45StockWords, 5, s45Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s45Stock : Lower s45Mask s45StockWords s45Goal 5 := dagShiftLower (width := 64) pm0 s26Stock (by decide +kernel)
def s46Blob307495 : Nat := (cbits [0x844180e050380c0e,0x4281502854201100,0x81d0687430190486,0x10e078341e0b0783,0x20940a2510084022,0xb41a2d140a412291,0x582e150b84c2e160,0x360b0d86835180c4,0x1c0e46836190d84c,0xe8643a150e8343a,0x683c160f0383c1c,0xe02038040e1c0f,0xe0d0382c0e068381,0x6038540e13038380,0x4412110284400111,0x60110c0442811090,0x1506854081500854,0x1a05438150b05420,0x641a19040640219,0x470190e064341908,0x81d06074121d0287,0xe050780c1e0c0742,0xc078281e09078181,0x8412210288400210,0x6021140844821110,0x2506894082500894,0x1a09458251309440])
def s46Blob308066 : Nat := (cbits [0xfffc0000863fc7f8,0x79c03807fffc0fff,0x3f0000003ff0f,0xfe03fff07df33e67,0x81fc3f87fe03ff80,0x3ffff0003ffff,0xfffc00fffe003ff8,0xffffc0000003ffff,0xfffc0000000000ff])
def s46Blob308276 : Nat := (cbits [0xa180800001542a8,0x38c018030a180185,0x2020b0102021b107,0xec4ada705d732e65,0x81bc3786ec4956a4,0x48926b7648936cbb,0xf1e070ddee003d50,0xf7ea800081038c78,0xf1e00040810380ee])
def s46Mask : Nat := 0x7777777777777777
abbrev s46Goal : Nat := sGoal &&& s46Mask
abbrev s46StockWords : List Nat := [0x2222222222222222,0x4444444444444444,0x7070707070707070,0x7700770077007700,0x7777000077770000,0x7777777700000000]
def s46Fact : Nat × List Nat × Nat × Nat := (s46Mask, s46StockWords, 10, s46Goal)
def s46Cuts : List (Nat × List Nat × Nat × Nat) := [s17Fact, s16Fact, s20Fact, s43Fact, s44Fact, s26Fact, s45Fact, s8Fact]
def s46Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[14, 17, 33, 54, 58, 60, 14, 17, 33, 54, 58, 60, 13, 22, 26, 28, 38, 42, 44, 50, 52, 56, 13, 22], rfl⟩
def s46Witnesses := unpackWitnesses s46StockWords [8720, 269324, 531466, 793606, 1057281, 1327617]
def s46Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0xb81522a039c0e801,0x8264cc81902e45c0,0x3c4744e81d03]) else (if j < 2 then (cbits [0x1a23044284508201,0xa99502a05229c9,0x680c89903026]) else (cbits [0xf0bc2780ec5d0b46,0x822fc9]))) 11 (i % 16)
def s46Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x512314020120003f,0x272831f1c31b1a31,0x62132620a832b9c3,0x292c4a62b3e6273a,0x631404008ba92db]) else (cbits [0x70c6208a3270a31b,0x2c086208c92c1062,0x6200e92c08620889,0x692c9492c1862714,0x226281e0100401c1])) else (if j < 3 then (cbits [0x8266202462420314,0x382e9322a9302231,0x6242c92c2431830c,0x46200c31e3402b26,0x3892d3692cb062b1]) else (if j < 4 then (cbits [0x83c9321692c0e62a,0x201831410012b8c3,0xc38469343c92c406,0x83244462442934bc,0x4c33044620426204]) else 0x4862446624))) 20 (i % 16)
def s46Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x400808024080fc0,0x200863611880418a,0x86280989c24960e6,0xa0989ca496166202,0x81e31b0462]) else (if j < 2 then (cbits [0x2662448c5078c510,0x2c59260a8c7c1310,0x8c400b0e154992a9,0x20a4b5a4963402b6,0x3138293278c4]) else (cbits [0x4062489269098820,0x3098c5608c92449a,0x3]))) 19 (i % 16)
def s46Links := pageLinks s46Index s46Codes 4 13 6 5
def s46Data (i : Nat) : Nat × Nat :=
  let e := s46Forest i
  (e &&& 63, e >>> 6)
def s46Sample : Nat × Nat := (s46Blob307495, 96)
def s46Tags := dagTraceTags s46Mask 96 (dagTagBases s46StockWords s46Blob308066 s46Blob308276 96) 9 s46Data
def s46States := dagTrace s46Mask s46StockWords 9 s46Data
def s46MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)))]
def s46Moves := dagMoves s46MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Autos : DagMovesOK s46Mask s46Goal 64 s46Moves := dagMovesOfCheck (by decide +kernel)
def s46Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x2700000767ee07,0x6f6f6f2000076f20]) else (if j < 2 then (cbits [0x40002f2f000f6f00,0xef006f0007002750]) else 0x6f6f0f2f000000)) 8 (i % 16)
def s46Check := dagCheckNode s46Mask s46Goal s46Chart (fun i => dagKnownCloses s46Goal (cutPick s46Cuts (s46Choice i))) 39 s46States s46Moves s46Links s46Sample s46Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Roots : dagCheckRoots s46Mask s46Goal s46Chart (dagKnownCloses s46Goal s46Cuts) s46Witnesses (dagRef 39 s46States s46Moves s46Links 0) s46StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block0 : treeBlock 0 24 s46Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Block24 : treeBlock 24 15 s46Check = true := by decide +kernel
theorem s46Group0_39 : treeBlock 0 39 s46Check = true := treeBlock_merge (start := 0) (left := 24) (right := 15) (check := s46Check) s46Block0 s46Block24
theorem s46Blocks : treeBlock 0 39 s46Check = true := s46Group0_39
theorem s46Known : Known s46Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s8Stock) s45Stock) s26Stock) s44Stock) s43Stock) s20Stock) s16Stock) s17Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s46Stock : Lower s46Mask s46StockWords s46Goal 10 := by
  apply lowerDag s46Choice _ _ _ _ s46Autos _ _ _ s46Known _ s46Roots s46Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s46Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s47Mask : Nat := 0xccccccccffffffff
abbrev s47Goal : Nat := sGoal &&& s47Mask
abbrev s47StockWords : List Nat := [0x88888888aaaaaaaa,0xcccccccccccccccc,0xc0c0c0c0f0f0f0f0,0xcc00cc00ff00ff00,0xcccc0000ffff0000,0xcccccccc00000000]
def s47Fact : Nat × List Nat × Nat × Nat := (s47Mask, s47StockWords, 10, s47Goal)
def s47Witnesses := unpackWitnesses s47StockWords [3590, 265733, 527875, 792067, 1057281, 1328643]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s47Stock : Lower s47Mask s47StockWords s47Goal 10 := by
  apply essentialLift (witnesses := s47Witnesses) (cut := s12Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s12StockWords) (by decide +kernel)
  · exact s12Stock
  · decide +kernel
def s48Mask : Nat := 0xccccffffccccffff
abbrev s48Goal : Nat := sGoal &&& s48Mask
abbrev s48StockWords : List Nat := [0x8888aaaa8888aaaa,0xcccccccccccccccc,0xc0c0f0f0c0c0f0f0,0xcc00ff00cc00ff00,0xcccc0000cccc0000,0xccccffff00000000]
def s48Fact : Nat × List Nat × Nat × Nat := (s48Mask, s48StockWords, 10, s48Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s48Stock : Lower s48Mask s48StockWords s48Goal 10 := dagShiftLower (width := 64) pm6 s47Stock (by decide +kernel)
def s49Mask : Nat := 0xccffccffccffccff
abbrev s49Goal : Nat := sGoal &&& s49Mask
abbrev s49StockWords : List Nat := [0x88aa88aa88aa88aa,0xcccccccccccccccc,0xc0f0c0f0c0f0c0f0,0xcc00cc00cc00cc00,0xccff0000ccff0000,0xccffccff00000000]
def s49Fact : Nat × List Nat × Nat × Nat := (s49Mask, s49StockWords, 10, s49Goal)
def s49Witnesses := unpackWitnesses s49StockWords [3590, 265733, 527875, 792067, 1057281, 1327617]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s49Stock : Lower s49Mask s49StockWords s49Goal 10 := by
  apply essentialLift (witnesses := s49Witnesses) (cut := s12Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s12StockWords) (by decide +kernel)
  · exact s12Stock
  · decide +kernel
def s50Mask : Nat := 0xcfcfcfcfcfcfcfcf
abbrev s50Goal : Nat := sGoal &&& s50Mask
abbrev s50StockWords : List Nat := [0x8a8a8a8a8a8a8a8a,0xcccccccccccccccc,0xc0c0c0c0c0c0c0c0,0xcf00cf00cf00cf00,0xcfcf0000cfcf0000,0xcfcfcfcf00000000]
def s50Fact : Nat × List Nat × Nat × Nat := (s50Mask, s50StockWords, 10, s50Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s50Stock : Lower s50Mask s50StockWords s50Goal 10 := dagShiftLower (width := 64) pm0 s49Stock (by decide +kernel)
def s51Mask : Nat := 0xeeeeeeeeeeeeeeee
abbrev s51Goal : Nat := sGoal &&& s51Mask
abbrev s51StockWords : List Nat := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xe0e0e0e0e0e0e0e0,0xee00ee00ee00ee00,0xeeee0000eeee0000,0xeeeeeeee00000000]
def s51Fact : Nat × List Nat × Nat × Nat := (s51Mask, s51StockWords, 10, s51Goal)
def s51Witnesses := unpackWitnesses s51StockWords [3590, 265733, 527875, 792067, 1057281, 1327617]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s51Stock : Lower s51Mask s51StockWords s51Goal 10 := by
  apply essentialLift (witnesses := s51Witnesses) (cut := s12Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s12StockWords) (by decide +kernel)
  · exact s12Stock
  · decide +kernel
def s52Mask : Nat := 0xf0f0f0f0ffffffff
abbrev s52Goal : Nat := sGoal &&& s52Mask
abbrev s52StockWords : List Nat := [0xa0a0a0a0aaaaaaaa,0xc0c0c0c0cccccccc,0xf0f0f0f0f0f0f0f0,0xf000f000ff00ff00,0xf0f00000ffff0000,0xf0f0f0f000000000]
def s52Fact : Nat × List Nat × Nat × Nat := (s52Mask, s52StockWords, 10, s52Goal)
def s52Witnesses := unpackWitnesses s52StockWords [3590, 265733, 527875, 792067, 1057281, 1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s52Stock : Lower s52Mask s52StockWords s52Goal 10 := by
  apply essentialLift (witnesses := s52Witnesses) (cut := s31Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s31StockWords) (by decide +kernel)
  · exact s31Stock
  · decide +kernel
def s53Mask : Nat := 0xf0f0fffff0f0ffff
abbrev s53Goal : Nat := sGoal &&& s53Mask
abbrev s53StockWords : List Nat := [0xa0a0aaaaa0a0aaaa,0xc0c0ccccc0c0cccc,0xf0f0f0f0f0f0f0f0,0xf000ff00f000ff00,0xf0f00000f0f00000,0xf0f0ffff00000000]
def s53Fact : Nat × List Nat × Nat × Nat := (s53Mask, s53StockWords, 10, s53Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s53Stock : Lower s53Mask s53StockWords s53Goal 10 := dagShiftLower (width := 64) pm6 s52Stock (by decide +kernel)
def s54Mask : Nat := 0xf0fff0fff0fff0ff
abbrev s54Goal : Nat := sGoal &&& s54Mask
abbrev s54StockWords : List Nat := [0xa0aaa0aaa0aaa0aa,0xc0ccc0ccc0ccc0cc,0xf0f0f0f0f0f0f0f0,0xf000f000f000f000,0xf0ff0000f0ff0000,0xf0fff0ff00000000]
def s54Fact : Nat × List Nat × Nat × Nat := (s54Mask, s54StockWords, 10, s54Goal)
def s54Witnesses := unpackWitnesses s54StockWords [3590, 265733, 527875, 793606, 1057281, 1327617]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s54Stock : Lower s54Mask s54StockWords s54Goal 10 := by
  apply essentialLift (witnesses := s54Witnesses) (cut := s31Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s31StockWords) (by decide +kernel)
  · exact s31Stock
  · decide +kernel
def s55Mask : Nat := 0xf3f3f3f3f3f3f3f3
abbrev s55Goal : Nat := sGoal &&& s55Mask
abbrev s55StockWords : List Nat := [0xa2a2a2a2a2a2a2a2,0xc0c0c0c0c0c0c0c0,0xf0f0f0f0f0f0f0f0,0xf300f300f300f300,0xf3f30000f3f30000,0xf3f3f3f300000000]
def s55Fact : Nat × List Nat × Nat × Nat := (s55Mask, s55StockWords, 10, s55Goal)
def s55Witnesses := unpackWitnesses s55StockWords [3590, 265733, 555064, 793606, 1057281, 1327617]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s55Stock : Lower s55Mask s55StockWords s55Goal 10 := by
  apply essentialLift (witnesses := s55Witnesses) (cut := s31Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s31StockWords) (by decide +kernel)
  · exact s31Stock
  · decide +kernel
def s56Mask : Nat := 0xfafafafafafafafa
abbrev s56Goal : Nat := sGoal &&& s56Mask
abbrev s56StockWords : List Nat := [0xaaaaaaaaaaaaaaaa,0xc8c8c8c8c8c8c8c8,0xf0f0f0f0f0f0f0f0,0xfa00fa00fa00fa00,0xfafa0000fafa0000,0xfafafafa00000000]
def s56Fact : Nat × List Nat × Nat × Nat := (s56Mask, s56StockWords, 10, s56Goal)
def s56Witnesses := unpackWitnesses s56StockWords [3590, 265733, 527875, 792067, 1057281, 1327617]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s56Stock : Lower s56Mask s56StockWords s56Goal 10 := by
  apply essentialLift (witnesses := s56Witnesses) (cut := s31Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s31StockWords) (by decide +kernel)
  · exact s31Stock
  · decide +kernel
def s57Mask : Nat := 0xfcfcfcfcfcfcfcfc
abbrev s57Goal : Nat := sGoal &&& s57Mask
abbrev s57StockWords : List Nat := [0xa8a8a8a8a8a8a8a8,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xfc00fc00fc00fc00,0xfcfc0000fcfc0000,0xfcfcfcfc00000000]
def s57Fact : Nat × List Nat × Nat × Nat := (s57Mask, s57StockWords, 10, s57Goal)
def s57Witnesses := unpackWitnesses s57StockWords [3590, 265733, 527875, 792067, 1058307, 1328643]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s57Stock : Lower s57Mask s57StockWords s57Goal 10 := by
  apply essentialLift (witnesses := s57Witnesses) (cut := s12Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s12StockWords) (by decide +kernel)
  · exact s12Stock
  · decide +kernel
def s58Mask : Nat := 0xff00ff00ffffffff
abbrev s58Goal : Nat := sGoal &&& s58Mask
abbrev s58StockWords : List Nat := [0xaa00aa00aaaaaaaa,0xcc00cc00cccccccc,0xf000f000f0f0f0f0,0xff00ff00ff00ff00,0xff000000ffff0000,0xff00ff0000000000]
def s58Fact : Nat × List Nat × Nat × Nat := (s58Mask, s58StockWords, 10, s58Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s58Stock : Lower s58Mask s58StockWords s58Goal 10 := dagShiftLower (width := 64) pm0 s52Stock (by decide +kernel)
def s59Mask : Nat := 0xff00ffffff00ffff
abbrev s59Goal : Nat := sGoal &&& s59Mask
abbrev s59StockWords : List Nat := [0xaa00aaaaaa00aaaa,0xcc00cccccc00cccc,0xf000f0f0f000f0f0,0xff00ff00ff00ff00,0xff000000ff000000,0xff00ffff00000000]
def s59Fact : Nat × List Nat × Nat × Nat := (s59Mask, s59StockWords, 10, s59Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s59Stock : Lower s59Mask s59StockWords s59Goal 10 := dagShiftLower (width := 64) pm9 s52Stock (by decide +kernel)
def s60Mask : Nat := 0xff0fff0fff0fff0f
abbrev s60Goal : Nat := sGoal &&& s60Mask
abbrev s60StockWords : List Nat := [0xaa0aaa0aaa0aaa0a,0xcc0ccc0ccc0ccc0c,0xf000f000f000f000,0xff00ff00ff00ff00,0xff0f0000ff0f0000,0xff0fff0f00000000]
def s60Fact : Nat × List Nat × Nat × Nat := (s60Mask, s60StockWords, 10, s60Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s60Stock : Lower s60Mask s60StockWords s60Goal 10 := dagShiftLower (width := 64) pm0 s54Stock (by decide +kernel)
def s61Mask : Nat := 0xff33ff33ff33ff33
abbrev s61Goal : Nat := sGoal &&& s61Mask
abbrev s61StockWords : List Nat := [0xaa22aa22aa22aa22,0xcc00cc00cc00cc00,0xf030f030f030f030,0xff00ff00ff00ff00,0xff330000ff330000,0xff33ff3300000000]
def s61Fact : Nat × List Nat × Nat × Nat := (s61Mask, s61StockWords, 10, s61Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s61Stock : Lower s61Mask s61StockWords s61Goal 10 := dagShiftLower (width := 64) pm0 s55Stock (by decide +kernel)
def s62Mask : Nat := 0xffaaffaaffaaffaa
abbrev s62Goal : Nat := sGoal &&& s62Mask
abbrev s62StockWords : List Nat := [0xaaaaaaaaaaaaaaaa,0xcc88cc88cc88cc88,0xf0a0f0a0f0a0f0a0,0xff00ff00ff00ff00,0xffaa0000ffaa0000,0xffaaffaa00000000]
def s62Fact : Nat × List Nat × Nat × Nat := (s62Mask, s62StockWords, 10, s62Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s62Stock : Lower s62Mask s62StockWords s62Goal 10 := dagShiftLower (width := 64) pm0 s56Stock (by decide +kernel)
def s63Mask : Nat := 0xffccffccffccffcc
abbrev s63Goal : Nat := sGoal &&& s63Mask
abbrev s63StockWords : List Nat := [0xaa88aa88aa88aa88,0xcccccccccccccccc,0xf0c0f0c0f0c0f0c0,0xff00ff00ff00ff00,0xffcc0000ffcc0000,0xffccffcc00000000]
def s63Fact : Nat × List Nat × Nat × Nat := (s63Mask, s63StockWords, 10, s63Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s63Stock : Lower s63Mask s63StockWords s63Goal 10 := dagShiftLower (width := 64) pm0 s57Stock (by decide +kernel)
def s64Mask : Nat := 0xfff0fff0fff0fff0
abbrev s64Goal : Nat := sGoal &&& s64Mask
abbrev s64StockWords : List Nat := [0xaaa0aaa0aaa0aaa0,0xccc0ccc0ccc0ccc0,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xfff00000fff00000,0xfff0fff000000000]
def s64Fact : Nat × List Nat × Nat × Nat := (s64Mask, s64StockWords, 10, s64Goal)
def s64Witnesses := unpackWitnesses s64StockWords [3590, 265733, 531466, 793606, 1059333, 1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s64Stock : Lower s64Mask s64StockWords s64Goal 10 := by
  apply essentialLift (witnesses := s64Witnesses) (cut := s31Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s31StockWords) (by decide +kernel)
  · exact s31Stock
  · decide +kernel
def s65Mask : Nat := 0xffff00000000ffff
abbrev s65Goal : Nat := sGoal &&& s65Mask
abbrev s65StockWords : List Nat := [0xaaaa00000000aaaa,0xcccc00000000cccc,0xf0f000000000f0f0,0xff0000000000ff00,0xffff000000000000]
def s65Fact : Nat × List Nat × Nat × Nat := (s65Mask, s65StockWords, 8, s65Goal)
def s65Witnesses := unpackWitnesses s65StockWords [3590, 265733, 527875, 792067, 1073665]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s65Stock : Lower s65Mask s65StockWords s65Goal 8 := by
  apply essentialLift (witnesses := s65Witnesses) (cut := s1Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s1StockWords) (by decide +kernel)
  · exact s1Stock
  · decide +kernel
def s66Mask : Nat := 0xffff0000ffff0000
abbrev s66Goal : Nat := sGoal &&& s66Mask
abbrev s66StockWords : List Nat := [0xaaaa0000aaaa0000,0xcccc0000cccc0000,0xf0f00000f0f00000,0xff000000ff000000,0xffff000000000000]
def s66Fact : Nat × List Nat × Nat × Nat := (s66Mask, s66StockWords, 8, s66Goal)
def s66Witnesses := unpackWitnesses s66StockWords [8720, 277532, 539674, 801814, 1076246]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s66Stock : Lower s66Mask s66StockWords s66Goal 8 := by
  apply essentialLift (witnesses := s66Witnesses) (cut := s16Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s16StockWords) (by decide +kernel)
  · exact s16Stock
  · decide +kernel
def s67Mask : Nat := 0xffffffff00000000
abbrev s67Goal : Nat := sGoal &&& s67Mask
abbrev s67StockWords : List Nat := [0xaaaaaaaa00000000,0xcccccccc00000000,0xf0f0f0f000000000,0xff00ff0000000000,0xffff000000000000]
def s67Fact : Nat × List Nat × Nat × Nat := (s67Mask, s67StockWords, 8, s67Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s67Stock : Lower s67Mask s67StockWords s67Goal 8 := dagShiftLower (width := 64) pm6 s66Stock (by decide +kernel)
def s68Mask : Nat := 0xffff0000ffff
abbrev s68Goal : Nat := sGoal &&& s68Mask
abbrev s68StockWords : List Nat := [0xaaaa0000aaaa,0xcccc0000cccc,0xf0f00000f0f0,0xff000000ff00,0xffff00000000]
def s68Fact : Nat × List Nat × Nat × Nat := (s68Mask, s68StockWords, 7, s68Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s68Stock : Lower s68Mask s68StockWords s68Goal 7 := dagShiftLower (width := 64) pm6 s37Stock (by decide +kernel)
def pm32 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12, st13, st45]
def s69Mask : Nat := 0xff00ff0000000000
abbrev s69Goal : Nat := sGoal &&& s69Mask
abbrev s69StockWords : List Nat := [0xaa00aa0000000000,0xcc00cc0000000000,0xf000f00000000000,0xff00000000000000]
def s69Fact : Nat × List Nat × Nat × Nat := (s69Mask, s69StockWords, 5, s69Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s69Stock : Lower s69Mask s69StockWords s69Goal 5 := dagShiftLower (width := 64) pm32 s9Stock (by decide +kernel)
def st14 : List (Nat × Nat) × List (Nat × Nat) := ([( 0xcccc3333cccc3333,0),(0xcccc0000cccc,14)],[(0x3333000033330000,14)])
def pm33 : List (List (Nat × Nat) × List (Nat × Nat)) := [st12, st13, st15, st14]
def s70Mask : Nat := 0xffff000000000000
abbrev s70Goal : Nat := sGoal &&& s70Mask
abbrev s70StockWords : List Nat := [0xaaaa000000000000,0xcccc000000000000,0xf0f0000000000000,0xff00000000000000]
def s70Fact : Nat × List Nat × Nat × Nat := (s70Mask, s70StockWords, 5, s70Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s70Stock : Lower s70Mask s70StockWords s70Goal 5 := dagShiftLower (width := 64) pm33 s9Stock (by decide +kernel)
def s71Blob358104 : Nat := (cbits [0x82c0c070281c0607,0x80c0e0502c120b01,0x2210683c180e0503,0x51108c0623100840,0x48a44c27120940a2,0xb41a2d150ac50290,0x582e150b84c2e160,0x361a0d46433180c4,0x1c0e46836190d84c,0xf0703a190e8543a,0xc02071c0f0683c16,0xc070681c08070101,0xb0402c040b0082c4,0x2038040e1502c1a0,0x384c0e06838100e0,0xa0f0183c580e150,0xf0503c120f0303c,0x288406210008418,0x844821110841221,0xc04230088c602114,0x4231508c4c231008,0x5068940825008946,0xa094582513094402,0x9c0c270289c06271,0x1029008a44827110,0x29150a44029068a4,0x48ac062b1c0a458])
def s71Blob358674 : Nat := (cbits [0xff80ffc08e3ffe3f,0x75c933ffffffffff,0xc07c07e01fffffc7,0x1fff07f879f1c3c7,0x81fe03f8007ff800,0xff8000001ffff83f,0x3ffe000000,0xfffffc0000000000,0xffffffffe000003f])
def s71Blob358884 : Nat := (cbits [0xc5884a400012561b,0x34c930edc28c2821,0x483487424ab19483,0x935a47185971c346,0x81be03b0125bb104,0xbb0122091c6ce22d,0x36ee000000,0xffeda80020020410,0x3c63c79e0070843f])
def s71Mask : Nat := 0xffffffff0000ffff
abbrev s71Goal : Nat := sGoal &&& s71Mask
abbrev s71StockWords : List Nat := [0xaaaaaaaa0000aaaa,0xcccccccc0000cccc,0xf0f0f0f00000f0f0,0xff00ff000000ff00,0xffff000000000000,0xffffffff00000000]
def s71Fact : Nat × List Nat × Nat × Nat := (s71Mask, s71StockWords, 10, s71Goal)
def s71Cuts : List (Nat × List Nat × Nat × Nat) := [s65Fact, s67Fact, s19Fact, s20Fact, s1Fact, s68Fact, s36Fact, s29Fact, s69Fact, s70Fact]
def s71Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 11, 14, 33, 54, 58, 60, 7, 11, 14, 33, 54, 3, 13, 38, 42, 44, 50, 52, 56, 3, 13, 38, 42], rfl⟩
def s71Witnesses := unpackWitnesses s71StockWords [3590, 265733, 527875, 792067, 1076262, 1327617]
def s71Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0xc01802c43640e001,0x44680c8990302600,0x4808c5181c73]) else (cbits [0x302604a294128241,0xc01712e05c09a1,0x6e0c95813006])) else (if j < 3 then (cbits [0x12c20823005bcb70,0x632c2584b09611d2,0xac34926acc19]) else (cbits [0x5c4b45646c0d71,0xc13803]))) 11 (i % 16)
def s71Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x71631b023140003f,0x273a6212a6209632,0x92c666375862b406,0xcc38e6937ba92daa,0xc6270a621046206]) else (if j < 2 then (cbits [0xd8492c126371062b,0x2c14c38929378a92,0x6240e93408c38069,0x831488c380892c0e,0x2292c1e6321a3321]) else (cbits [0x28f4426c3824932,0x2b20630209301c01,0x627046202e0372c0,0x69373492d3092ca6,0x32c380692c38c383]))) else (if j < 5 then (if j < 4 then (cbits [0x50a62032c380892c,0x44b4c383c9322262,0x3251a3190c3143ef,0xc92c42620a433124,0x56f44bcc38489343]) else (cbits [0x40e3144662444934,0x3844620523254a32,0x6204e32b4c31454c,0x4c40506305092c46,0x623315a330103145])) else (if j < 6 then (cbits [0x75c31464f4448624,0x2460c384a6245e33,0x930509304e6244c6,0x2314549306063c52,0x6a93db692c6833d1]) else (cbits [0xca86332862714620,0x37569333e92d3892,0xbec39b8c38649])))) 20 (i % 16)
def s71Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x662008628080fc0,0x2708c42130e03496,0x8c6e118ac249a0e6,0x460c50c18d82c380,0x319180103866]) else (cbits [0x1893231258624c10,0x2b58c400bd10c61c,0x9870ca4b1601bac0,0x20b0e1649bac92d5,0x7a23c93278c4])) else (if j < 3 then (cbits [0x4693488c410989c1,0x14986492a4d21312,0x464b2a4b26195cc3,0x1698ac17a242c389,0x19bdc314b866]) else (cbits [0x82f44b46636b0e2e,0x380527ba0cf7431b,0xc]))) 19 (i % 16)
def s71Links := pageLinks s71Index s71Codes 4 13 6 5
def s71Data (i : Nat) : Nat × Nat :=
  let e := s71Forest i
  (e &&& 63, e >>> 6)
def s71Sample : Nat × Nat := (s71Blob358104, 96)
def s71Tags := dagTraceTags s71Mask 96 (dagTagBases s71StockWords s71Blob358674 s71Blob358884 96) 9 s71Data
def s71States := dagTrace s71Mask s71StockWords 9 s71Data
def s71MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)))]
def s71Moves := dagMoves s71MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Autos : DagMovesOK s71Mask s71Goal 64 s71Moves := dagMovesOfCheck (by decide +kernel)
def s71Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0xf0fc3e,0x40cf80f080300000,0x22000808]) else (cbits [0x2fc020091800888,0xf080000000f0000,0xef8])) else (if j < 3 then (cbits [0x388e00000003be,0xbe00000000000000,0x639]) else (cbits [0xf000222fe0004800,0x3]))) 10 (i % 16)
def s71Check := dagCheckNode s71Mask s71Goal s71Chart (fun i => dagKnownCloses s71Goal (cutPick s71Cuts (s71Choice i))) 55 s71States s71Moves s71Links s71Sample s71Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Roots : dagCheckRoots s71Mask s71Goal s71Chart (dagKnownCloses s71Goal s71Cuts) s71Witnesses (dagRef 55 s71States s71Moves s71Links 0) s71StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Block0 : treeBlock 0 24 s71Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Block24 : treeBlock 24 24 s71Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Block48 : treeBlock 48 7 s71Check = true := by decide +kernel
theorem s71Group24_31 : treeBlock 24 31 s71Check = true := treeBlock_merge (start := 24) (left := 24) (right := 7) (check := s71Check) s71Block24 s71Block48
theorem s71Group0_55 : treeBlock 0 55 s71Check = true := treeBlock_merge (start := 0) (left := 24) (right := 31) (check := s71Check) s71Block0 s71Group24_31
theorem s71Blocks : treeBlock 0 55 s71Check = true := s71Group0_55
theorem s71Known : Known s71Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s70Stock) s69Stock) s29Stock) s36Stock) s68Stock) s1Stock) s20Stock) s19Stock) s67Stock) s65Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s71Stock : Lower s71Mask s71StockWords s71Goal 10 := by
  apply lowerDag s71Choice _ _ _ _ s71Autos _ _ _ s71Known _ s71Roots s71Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s71Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s72Mask : Nat := 0xffff0000ffffffff
abbrev s72Goal : Nat := sGoal &&& s72Mask
abbrev s72StockWords : List Nat := [0xaaaa0000aaaaaaaa,0xcccc0000cccccccc,0xf0f00000f0f0f0f0,0xff000000ff00ff00,0xffff0000ffff0000,0xffff000000000000]
def s72Fact : Nat × List Nat × Nat × Nat := (s72Mask, s72StockWords, 10, s72Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s72Stock : Lower s72Mask s72StockWords s72Goal 10 := dagShiftLower (width := 64) pm6 s71Stock (by decide +kernel)
def s73Blob363356 : Nat := (cbits [0x54140b0482c060b,0x82c1e0e0742c170a,0xb0102c020b0e07,0x70e0542c15008541,0xa074121d0a05c061,0x7c2c1f0a078141e0,0x61500054000b0e0,0x170105c021704854,0xb074101d0087438,0x87c061f04078041e,0xc2c0b0a07c141f04,0x170405404150e02,0xd0007414170485c0,0x1878001e05074061,0x7c041f0087c121e0,0x101705054280b040,0x7c021e01074])
def s73Blob363721 : Nat := (cbits [0x7bf8fffcfff3ff3f,0xf8d7f1cff1c7cc7d,0x7e7fbfff3fffbff8,0xe7fe0ffe07f0])
def s73Blob363833 : Nat := (cbits [0x540e480c27014903,0xf8292d1558914525,0x4a604000e0903ab0,0x1a49a9a52252])
def s73Mask : Nat := 0xf0f00f0f
abbrev s73Goal : Nat := sGoal &&& s73Mask
abbrev s73StockWords : List Nat := [0xa0a00a0a,0xc0c00c0c,0xf0f00000,0xf0000f00]
def s73Cuts : List (Nat × List Nat × Nat × Nat) := []
def s73Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[11, 21, 30, 11, 21, 30, 11, 21, 30, 11, 21, 30, 3, 9, 10, 22, 28, 3, 9, 10, 22, 28, 3, 9], rfl⟩
def s73Witnesses := unpackWitnesses s73StockWords [5642, 267785, 535041, 792067]
def s73Index (i : Nat) : Nat := unpack 0x119 3 i
def s73Codes (i : Nat) : Nat := unpack 0x2324000f 16 i
def s73Forest (i : Nat) : Nat := unpack 0x648803c 15 i
def s73Links := pageLinks s73Index s73Codes 1 13 2 2
def s73Data (i : Nat) : Nat × Nat :=
  let e := s73Forest i
  (e &&& 3, e >>> 2)
def s73Sample : Nat × Nat := (s73Blob363356, 60)
def s73Tags := dagTraceTags s73Mask 60 (dagTagBases s73StockWords s73Blob363721 s73Blob363833 60) 4 s73Data
def s73States := dagTrace s73Mask s73StockWords 4 s73Data
def s73MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s73Moves := dagMoves s73MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Autos : DagMovesOK s73Mask s73Goal 64 s73Moves := dagMovesOfCheck (by decide +kernel)
def s73Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack 0x0 1 (i % 16)
def s73Check := dagCheckNode s73Mask s73Goal s73Chart (fun i => dagKnownCloses s73Goal (cutPick s73Cuts (s73Choice i))) 2 s73States s73Moves s73Links s73Sample s73Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Roots : dagCheckRoots s73Mask s73Goal s73Chart (dagKnownCloses s73Goal s73Cuts) s73Witnesses (dagRef 2 s73States s73Moves s73Links 0) s73StockWords 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Block0 : treeBlock 0 2 s73Check = true := by decide +kernel
theorem s73Blocks : treeBlock 0 2 s73Check = true := s73Block0
theorem s73Known : Known s73Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s73Stock : Lower s73Mask s73StockWords s73Goal 5 := by
  apply lowerDag s73Choice _ _ _ _ s73Autos _ _ _ s73Known _ s73Roots s73Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s73Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s74Mask : Nat := 0xff0000ff
abbrev s74Goal : Nat := sGoal &&& s74Mask
abbrev s74StockWords : List Nat := [0xaa0000aa,0xcc0000cc,0xf00000f0,0xff000000]
def s74Fact : Nat × List Nat × Nat × Nat := (s74Mask, s74StockWords, 5, s74Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s74Stock : Lower s74Mask s74StockWords s74Goal 5 := dagShiftLower (width := 64) pm0 s73Stock (by decide +kernel)
def s75Blob366871 : Nat := (cbits [0x8402210b05c2413,0x86433120940a2510,0xc130084c64360b0d,0x10905c0a171904c2,0x894482102884002,0xd824331009408250,0x64370b0dc4836090,0x170085c0a130004c,0x1908408211905c08,0xcc2c33008cc0025,0xc0a37100d8083610,0x130204c4837090d,0x50908448170005c4,0x28cc0033190942c2,0xdc0a36000d848330,0x4813100dc0837008,0x33090942c211005c,0x37008d808])
def s75Blob367256 : Nat := (cbits [0xdfe7ffcfff9ffe7f,0xb9ff8fff1ff81fe1,0x9abe367c4e7b8c6c,0xf9ffc3ff83ff83f])
def s75Blob367371 : Nat := (cbits [0xa03200420c029214,0x8600704250d816e1,0x55594d51531652c,0x7092a51429212d])
def s75Mask : Nat := 0xcc003300cc0033
abbrev s75Goal : Nat := sGoal &&& s75Mask
abbrev s75StockWords : List Nat := [0x88002200880022,0xcc000000cc0000,0xc0003000c00030,0xcc003300000000]
def s75Fact : Nat × List Nat × Nat × Nat := (s75Mask, s75StockWords, 5, s75Goal)
def s75Cuts : List (Nat × List Nat × Nat × Nat) := []
def s75Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[19, 33, 54, 19, 33, 54, 19, 33, 54, 19, 33, 54, 5, 22, 36, 50, 5, 22, 36, 50, 5, 22, 36, 50], rfl⟩
def s75Witnesses := unpackWitnesses s75StockWords [9746, 271873, 551986, 803329]
def s75Index (i : Nat) : Nat := unpack 0x9 2 i
def s75Codes (i : Nat) : Nat := unpack 0xf 15 i
def s75Forest (i : Nat) : Nat := unpack 0x1e 14 i
def s75Links := pageLinks s75Index s75Codes 1 13 1 2
def s75Data (i : Nat) : Nat × Nat :=
  let e := s75Forest i
  (e &&& 1, e >>> 1)
def s75Sample : Nat × Nat := (s75Blob366871, 63)
def s75Tags := dagTraceTags s75Mask 63 (dagTagBases s75StockWords s75Blob367256 s75Blob367371 63) 4 s75Data
def s75States := dagTrace s75Mask s75StockWords 4 s75Data
def s75MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s75Moves := dagMoves s75MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Autos : DagMovesOK s75Mask s75Goal 64 s75Moves := dagMovesOfCheck (by decide +kernel)
def s75Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack 0x0 1 (i % 16)
def s75Check := dagCheckNode s75Mask s75Goal s75Chart (fun i => dagKnownCloses s75Goal (cutPick s75Cuts (s75Choice i))) 1 s75States s75Moves s75Links s75Sample s75Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Roots : dagCheckRoots s75Mask s75Goal s75Chart (dagKnownCloses s75Goal s75Cuts) s75Witnesses (dagRef 1 s75States s75Moves s75Links 0) s75StockWords 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Block0 : treeBlock 0 1 s75Check = true := by decide +kernel
theorem s75Blocks : treeBlock 0 1 s75Check = true := s75Block0
theorem s75Known : Known s75Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s75Stock : Lower s75Mask s75StockWords s75Goal 5 := by
  apply lowerDag s75Choice _ _ _ _ s75Autos _ _ _ s75Known _ s75Roots s75Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s75Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s76Mask : Nat := 0xf00000f0f00000f
abbrev s76Goal : Nat := sGoal &&& s76Mask
abbrev s76StockWords : List Nat := [0xa00000a0a00000a,0xc00000c0c00000c,0xf0000000f000000,0xf00000f00000000]
def s76Fact : Nat × List Nat × Nat × Nat := (s76Mask, s76StockWords, 5, s76Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s76Stock : Lower s76Mask s76StockWords s76Goal 5 := dagShiftLower (width := 64) pm17 s75Stock (by decide +kernel)
def pm34 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13]
def s77Mask : Nat := 0x3300003333000033
abbrev s77Goal : Nat := sGoal &&& s77Mask
abbrev s77StockWords : List Nat := [0x2200002222000022,0x3000003030000030,0x3300000033000000,0x3300003300000000]
def s77Fact : Nat × List Nat × Nat × Nat := (s77Mask, s77StockWords, 5, s77Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s77Stock : Lower s77Mask s77StockWords s77Goal 5 := dagShiftLower (width := 64) pm34 s75Stock (by decide +kernel)
def s78Mask : Nat := 0x4444111144441111
abbrev s78Goal : Nat := sGoal &&& s78Mask
abbrev s78StockWords : List Nat := [0x4444000044440000,0x4040101040401010,0x4400110044001100,0x4444111100000000]
def s78Fact : Nat × List Nat × Nat × Nat := (s78Mask, s78StockWords, 5, s78Goal)
def s78Witnesses := unpackWitnesses s78StockWords [15372, 277530, 539670, 814102]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s78Stock : Lower s78Mask s78StockWords s78Goal 5 := by
  apply essentialLift (witnesses := s78Witnesses) (cut := s7Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s7StockWords) (by decide +kernel)
  · exact s7Stock
  · decide +kernel
def s79Mask : Nat := 0x5500005555000055
abbrev s79Goal : Nat := sGoal &&& s79Mask
abbrev s79StockWords : List Nat := [0x4400004444000044,0x5000005050000050,0x5500000055000000,0x5500005500000000]
def s79Fact : Nat × List Nat × Nat × Nat := (s79Mask, s79StockWords, 5, s79Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s79Stock : Lower s79Mask s79StockWords s79Goal 5 := dagShiftLower (width := 64) pm17 s78Stock (by decide +kernel)
def s80Blob374434 : Nat := (cbits [0x782c170502c060b,0x8542b1108c06230b,0x6171502c040b0b0d,0x30108c2c1f050780,0x10ac142b018ac542,0xf82c3e0b0dc44361,0x41e0105c440b150,0x230507c061f15078,0x150d80436010ac14,0xf8143e110dc0637,0xc2c0b150fc2c3f11,0x41e0187844170505,0x60b08c541f0107c4,0x50dc0437050d8063,0xfc143f018fc043e1,0x2c2b1107c5417110,0x10fc063e050dc])
def s80Blob374804 : Nat := (cbits [0xcbfb39f33ccbf777,0x4beffdfbfcfbc1c8,0xf0dbc1e7c2f739b,0xf3fe03ff03fe])
def s80Blob374915 : Nat := (cbits [0xc408420104008411,0x4210020500018108,0x26025290a49a214a,0xe2152a82664])
def s80Mask : Nat := 0xc0c00c0cc0c00c0c
abbrev s80Goal : Nat := sGoal &&& s80Mask
abbrev s80StockWords : List Nat := [0x8080080880800808,0xc0c00000c0c00000,0xc0000c00c0000c00,0xc0c00c0c00000000]
def s80Cuts : List (Nat × List Nat × Nat × Nat) := []
def s80Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[11, 23, 30, 35, 54, 11, 23, 30, 35, 54, 11, 23, 3, 22, 42, 3, 22, 42, 3, 22, 42, 3, 22, 42], rfl⟩
def s80Witnesses := unpackWitnesses s80StockWords [5642, 273923, 529923, 804355]
def s80Index (i : Nat) : Nat := unpack 0x119 3 i
def s80Codes (i : Nat) : Nat := unpack 0x2628000f 16 i
def s80Forest (i : Nat) : Nat := unpack 0xc50803c 15 i
def s80Links := pageLinks s80Index s80Codes 1 13 2 2
def s80Data (i : Nat) : Nat × Nat :=
  let e := s80Forest i
  (e &&& 3, e >>> 2)
def s80Sample : Nat × Nat := (s80Blob374434, 60)
def s80Tags := dagTraceTags s80Mask 60 (dagTagBases s80StockWords s80Blob374804 s80Blob374915 60) 4 s80Data
def s80States := dagTrace s80Mask s80StockWords 4 s80Data
def s80MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s80Moves := dagMoves s80MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s80Autos : DagMovesOK s80Mask s80Goal 64 s80Moves := dagMovesOfCheck (by decide +kernel)
def s80Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack 0x0 1 (i % 16)
def s80Check := dagCheckNode s80Mask s80Goal s80Chart (fun i => dagKnownCloses s80Goal (cutPick s80Cuts (s80Choice i))) 2 s80States s80Moves s80Links s80Sample s80Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s80Roots : dagCheckRoots s80Mask s80Goal s80Chart (dagKnownCloses s80Goal s80Cuts) s80Witnesses (dagRef 2 s80States s80Moves s80Links 0) s80StockWords 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s80Block0 : treeBlock 0 2 s80Check = true := by decide +kernel
theorem s80Blocks : treeBlock 0 2 s80Check = true := s80Block0
theorem s80Known : Known s80Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s80Stock : Lower s80Mask s80StockWords s80Goal 5 := by
  apply lowerDag s80Choice _ _ _ _ s80Autos _ _ _ s80Known _ s80Roots s80Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s80Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s81Mask : Nat := 0xcc0000cccc0000cc
abbrev s81Goal : Nat := sGoal &&& s81Mask
abbrev s81StockWords : List Nat := [0x8800008888000088,0xc00000c0c00000c0,0xcc000000cc000000,0xcc0000cc00000000]
def s81Fact : Nat × List Nat × Nat × Nat := (s81Mask, s81StockWords, 5, s81Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s81Stock : Lower s81Mask s81StockWords s81Goal 5 := dagShiftLower (width := 64) pm0 s80Stock (by decide +kernel)
def s82Mask : Nat := 0xf00000f0f00000f0
abbrev s82Goal : Nat := sGoal &&& s82Mask
abbrev s82StockWords : List Nat := [0xa00000a0a00000a0,0xc00000c0c00000c0,0xf0000000f0000000,0xf00000f000000000]
def s82Fact : Nat × List Nat × Nat × Nat := (s82Mask, s82StockWords, 5, s82Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s82Stock : Lower s82Mask s82StockWords s82Goal 5 := dagShiftLower (width := 64) pm19 s80Stock (by decide +kernel)
def s83Mask : Nat := 0xff000000ff000000
abbrev s83Goal : Nat := sGoal &&& s83Mask
abbrev s83StockWords : List Nat := [0xaa000000aa000000,0xcc000000cc000000,0xf0000000f0000000,0xff00000000000000]
def s83Fact : Nat × List Nat × Nat × Nat := (s83Mask, s83StockWords, 5, s83Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s83Stock : Lower s83Mask s83StockWords s83Goal 5 := dagShiftLower (width := 64) pm17 s9Stock (by decide +kernel)
def s84Blob379193 : Nat := (cbits [0x640c070281c0607,0x8341e0e074341b0c,0x6231008402210e07,0x7120940a251108c0,0xc0e8343a1c0e44c2,0x1c02071c0f0383c1,0x2191301c0807010,0x1b1c06438190d064,0xc0740a1d0c06c06,0x7c341f0c0780c1e,0x40a210188400210e,0x4230088c48211108,0x5008944c231008c0,0x189c4c2510094082,0x9c44270309c0a270,0x443a0c0e83039120,0x3c0c0f0703b0d0ec,0xd0f8703d0e0f448,0x1c703e130f8383e,0x400191201c440700,0x41b0086c0a190186,0xd00874701b0e06c0,0x1078701d0d074081,0x7c701e13078081e0,0x301f0307c0a1f018,0x2113084082101084,0x308c0a230008c70])
def s84Blob379762 : Nat := (cbits [0x667ffffcfff0ff3f,0x30f34cd7ffe1fff8,0xe1fe1e3f87be1e0f,0xf83fe00fc0fc70e7,0xff0f80f801ffe03f,0x1ffffc7ffc0000f,0xfffffff0000fff00,0xfe000007])
def s84Blob379949 : Nat := (cbits [0x6226051101503,0x12a14c5540602380,0x8aaa8492831b14a5,0x302d514944c470a6,0xae0f80f8cccc4923,0x11119805eec0000e,0x55319980088aea00,0x18191036])
def s84Mask : Nat := 0xff0000ffff0000ff
abbrev s84Goal : Nat := sGoal &&& s84Mask
abbrev s84StockWords : List Nat := [0xaa0000aaaa0000aa,0xcc0000cccc0000cc,0xf00000f0f00000f0,0xff000000ff000000,0xff0000ff00000000]
def s84Fact : Nat × List Nat × Nat × Nat := (s84Mask, s84StockWords, 8, s84Goal)
def s84Cuts : List (Nat × List Nat × Nat × Nat) := [s74Fact, s76Fact, s77Fact, s79Fact, s81Fact, s82Fact, s83Fact, s14Fact]
def s84Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 25, 30, 33, 58, 60, 7, 25, 30, 33, 58, 60, 3, 5, 26, 28, 38, 56, 3, 5, 26, 28, 38, 56], rfl⟩
def s84Witnesses := unpackWitnesses s84StockWords [3590, 265733, 527875, 799233, 1065473]
def s84Index (i : Nat) : Nat := unpack (cbits [0x70545050503b0e01,0x8c88737070]) 8 i
def s84Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0xc50803708020001f,0x16c384a4b2a62028,0x3141b0e2462010c5,0x430e0e92c318804,0xba4b0e62]) else (cbits [0x4b1062018c514c38,0x14c38c2])) 18 (i % 16)
def s84Forest (i : Nat) : Nat := unpack (cbits [0x1c10c508010201f0,0x6318818628203716,0xb0e292582c38649,0x61c]) 17 i
def s84Links := pageLinks s84Index s84Codes 3 13 4 4
def s84Data (i : Nat) : Nat × Nat :=
  let e := s84Forest i
  (e &&& 15, e >>> 4)
def s84Sample : Nat × Nat := (s84Blob379193, 96)
def s84Tags := dagTraceTags s84Mask 96 (dagTagBases s84StockWords s84Blob379762 s84Blob379949 96) 7 s84Data
def s84States := dagTrace s84Mask s84StockWords 7 s84Data
def s84MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm15, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)))]
def s84Moves := dagMoves s84MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s84Autos : DagMovesOK s84Mask s84Goal 64 s84Moves := dagMovesOfCheck (by decide +kernel)
def s84Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (cbits [0x1000000817f,0x1008100]) 8 (i % 16)
def s84Check := dagCheckNode s84Mask s84Goal s84Chart (fun i => dagKnownCloses s84Goal (cutPick s84Cuts (s84Choice i))) 12 s84States s84Moves s84Links s84Sample s84Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s84Roots : dagCheckRoots s84Mask s84Goal s84Chart (dagKnownCloses s84Goal s84Cuts) s84Witnesses (dagRef 12 s84States s84Moves s84Links 0) s84StockWords 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s84Block0 : treeBlock 0 12 s84Check = true := by decide +kernel
theorem s84Blocks : treeBlock 0 12 s84Check = true := s84Block0
theorem s84Known : Known s84Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s14Stock) s83Stock) s82Stock) s81Stock) s79Stock) s77Stock) s76Stock) s74Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s84Stock : Lower s84Mask s84StockWords s84Goal 8 := by
  apply lowerDag s84Choice _ _ _ _ s84Autos _ _ _ s84Known _ s84Roots s84Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s84Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s85Blob383236 : Nat := (cbits [0x5c2011008440c07,0x44c271008402210b,0x207130d82c36180c,0x1000444c070b01c0,0x808400210305c601,0xc42031008c40c271,0x2c37180d80c36100,0x110b0440007130dc,0x1305c20170085c40,0x9c0227130842021,0x82036000c440270b,0x7180dc0c37100d,0x70005c0c111001c2,0x809c002703084601,0xdc0036130c42c311,0x6007100dc2037008,0x270b084401713044,0xdc0236030c420])
def s85Blob383625 : Nat := (cbits [0xbfefff3fff3ffcff,0xd5f36fdce7c49f49,0xe6fc73e0fbf8e38e,0xf8ff83ff03ff03f0])
def s85Blob383741 : Nat := (cbits [0x4020000420080412,0x2a0c910a8b449b49,0x194646494992498c,0x78a4a9292a252e0])
def s85Mask : Nat := 0xc300c300c300c3
abbrev s85Goal : Nat := sGoal &&& s85Mask
abbrev s85StockWords : List Nat := [0x82008200820082,0xc000c000c000c0,0xc3000000c30000,0xc300c300000000]
def s85Fact : Nat × List Nat × Nat × Nat := (s85Mask, s85StockWords, 6, s85Goal)
def s85Cuts : List (Nat × List Nat × Nat × Nat) := []
def s85Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 17, 33, 54, 7, 17, 33, 54, 7, 17, 33, 54, 1, 22, 38, 48, 1, 22, 38, 48, 1, 22, 38, 48], rfl⟩
def s85Witnesses := unpackWitnesses s85StockWords [3590, 265729, 532993, 803329]
def s85Index (i : Nat) : Nat := unpack 0x28a28301 6 i
def s85Codes (i : Nat) : Nat := unpack (cbits [0x31010c504010000f,0x1692c3]) 17 i
def s85Forest (i : Nat) : Nat := unpack 0x310118a100410078 16 i
def s85Links := pageLinks s85Index s85Codes 3 13 3 4
def s85Data (i : Nat) : Nat × Nat :=
  let e := s85Forest i
  (e &&& 7, e >>> 3)
def s85Sample : Nat × Nat := (s85Blob383236, 64)
def s85Tags := dagTraceTags s85Mask 64 (dagTagBases s85StockWords s85Blob383625 s85Blob383741 64) 5 s85Data
def s85States := dagTrace s85Mask s85StockWords 5 s85Data
def s85MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)))]
def s85Moves := dagMoves s85MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Autos : DagMovesOK s85Mask s85Goal 64 s85Moves := dagMovesOfCheck (by decide +kernel)
def s85Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack 0x0 1 (i % 16)
def s85Check := dagCheckNode s85Mask s85Goal s85Chart (fun i => dagKnownCloses s85Goal (cutPick s85Cuts (s85Choice i))) 4 s85States s85Moves s85Links s85Sample s85Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Roots : dagCheckRoots s85Mask s85Goal s85Chart (dagKnownCloses s85Goal s85Cuts) s85Witnesses (dagRef 4 s85States s85Moves s85Links 0) s85StockWords 5 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Block0 : treeBlock 0 4 s85Check = true := by decide +kernel
theorem s85Blocks : treeBlock 0 4 s85Check = true := s85Block0
theorem s85Known : Known s85Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s85Stock : Lower s85Mask s85StockWords s85Goal 6 := by
  apply lowerDag s85Choice _ _ _ _ s85Autos _ _ _ s85Known _ s85Roots s85Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s85Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s86Blob386986 : Nat := (cbits [0x8440c070281c0607,0x424130184c201100,0x190b05c28150285,0xe0b078381d0d06c3,0x8402210e078341,0x940a251108c06231,0x6433180c44c27120,0x36130d82c361a0d4,0xd0e870391a0d864,0xf0383c1c0e8643a,0xc04070081c703c1a,0x111301c2c070201,0x1090440a11018440,0x84c60110c044281,0x4c2c130804c04130,0x8150085464130d0,0x150e0542c1508054,0x305c0a170185c68,0x6402190a05c2417,0xc70190e064341908,0xa1d0c06c241b0186,0xe03078301d0a0740,0xb07c301e0a078241,0x8400210e07c341f0,0x4821110840a21018,0x230108c022318084,0x89464231308c40])
def s86Blob387550 : Nat := (cbits [0xffffffe043ff1fff,0xbd4cea67fffe1fff,0x7c0fe383e07e03e3,0xff8003fc3e70f387,0xc000fc00800ffc03,0xffffc0000001f,0xfffffc1fff80fff8,0xffff0000000fffff,0xfff000000000001f])
def s86Blob387763 : Nat := (cbits [0x60821820001500ab,0x9d4c6a6584600484,0x68a66191a4742b41,0xdd10538c2e70b386,0xc000dc00214aac22,0xd127008208016,0x1e79e11ff780ff50,0x7bea0000420fdb7b,0x738000401041021b])
def s86Mask : Nat := 0xffff00ffffff00ff
abbrev s86Goal : Nat := sGoal &&& s86Mask
abbrev s86StockWords : List Nat := [0xaaaa00aaaaaa00aa,0xcccc00cccccc00cc,0xf0f000f0f0f000f0,0xff000000ff000000,0xffff0000ffff0000,0xffff00ff00000000]
def s86Fact : Nat × List Nat × Nat × Nat := (s86Mask, s86StockWords, 10, s86Goal)
def s86Cuts : List (Nat × List Nat × Nat × Nat) := [s84Fact, s66Fact, s16Fact, s40Fact, s85Fact, s2Fact, s24Fact, s83Fact, s70Fact]
def s86Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 17, 30, 33, 54, 58, 60, 7, 17, 30, 33, 54, 3, 5, 22, 26, 28, 38, 50, 52, 56, 3, 5, 22], rfl⟩
def s86Witnesses := unpackWitnesses s86StockWords [3590, 265733, 527875, 801814, 1057281, 1327617]
def s86Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x13c0f0384a406401,0x505415054105400f,0x681a0555]) else (cbits [0x5841c5701c0701a2,0x21])) 10 (i % 16)
def s86Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x7e38c6c118a0003f,0xa4b2c31fc2620306,0x157a2a6f44492867,0xa28af4410c7e1188,0xd2581bd1067]) else (if j < 2 then (cbits [0x945192891a510314,0x8c98d18a17250a92,0xe9284892c28c4c4,0x102803745e8a83d1,0x952585989c53]) else (cbits [0x5871924631020c38,0x1161c5c949992]))) 19 (i % 16)
def s86Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x20cc40218a0407e0,0x5e8a27a208c7e27a,0x9481a520628818d8,0xd18a3467e192820c,0x496064a0]) else (cbits [0x20528617a2c1e890,0x7a28406f47a])) 18 (i % 16)
def s86Links := pageLinks s86Index s86Codes 4 13 5 5
def s86Data (i : Nat) : Nat × Nat :=
  let e := s86Forest i
  (e &&& 31, e >>> 5)
def s86Sample : Nat × Nat := (s86Blob386986, 96)
def s86Tags := dagTraceTags s86Mask 96 (dagTagBases s86StockWords s86Blob387550 s86Blob387763 96) 9 s86Data
def s86States := dagTrace s86Mask s86StockWords 9 s86Data
def s86MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm15, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 2, 1, 3, 4, 5] 0 i.val)))]
def s86Moves := dagMoves s86MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s86Autos : DagMovesOK s86Mask s86Goal 64 s86Moves := dagMovesOfCheck (by decide +kernel)
def s86Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x4e000009cde6e,0x6e104410020b7,0x3780]) else 0x3dc00b7fbc0067) 9 (i % 16)
def s86Check := dagCheckNode s86Mask s86Goal s86Chart (fun i => dagKnownCloses s86Goal (cutPick s86Cuts (s86Choice i))) 22 s86States s86Moves s86Links s86Sample s86Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s86Roots : dagCheckRoots s86Mask s86Goal s86Chart (dagKnownCloses s86Goal s86Cuts) s86Witnesses (dagRef 22 s86States s86Moves s86Links 0) s86StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s86Block0 : treeBlock 0 22 s86Check = true := by decide +kernel
theorem s86Blocks : treeBlock 0 22 s86Check = true := s86Block0
theorem s86Known : Known s86Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s70Stock) s83Stock) s24Stock) s2Stock) s85Stock) s40Stock) s16Stock) s66Stock) s84Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s86Stock : Lower s86Mask s86StockWords s86Goal 10 := by
  apply lowerDag s86Choice _ _ _ _ s86Autos _ _ _ s86Known _ s86Roots s86Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s86Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s87Mask : Nat := 0xffff0f0fffff0f0f
abbrev s87Goal : Nat := sGoal &&& s87Mask
abbrev s87StockWords : List Nat := [0xaaaa0a0aaaaa0a0a,0xcccc0c0ccccc0c0c,0xf0f00000f0f00000,0xff000f00ff000f00,0xffff0000ffff0000,0xffff0f0f00000000]
def s87Fact : Nat × List Nat × Nat × Nat := (s87Mask, s87StockWords, 10, s87Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s87Stock : Lower s87Mask s87StockWords s87Goal 10 := dagShiftLower (width := 64) pm0 s86Stock (by decide +kernel)
def s88Mask : Nat := 0xc0c03030c0c0303
abbrev s88Goal : Nat := sGoal &&& s88Mask
abbrev s88StockWords : List Nat := [0x808020208080202,0xc0c00000c0c0000,0xc0003000c000300,0xc0c030300000000]
def s88Fact : Nat × List Nat × Nat × Nat := (s88Mask, s88StockWords, 5, s88Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s88Stock : Lower s88Mask s88StockWords s88Goal 5 := dagShiftLower (width := 64) pm0 s75Stock (by decide +kernel)
def s89Blob392053 : Nat := (cbits [0x940a250b0782c17,0xc2c36160b41a2d12,0xc1f0687c181e0285,0xd160941a25020942,0x20d8482d060b40a2,0x5c583e0b0f82c371,0x1a1e020781a17020,0x250607c0a1f16078,0x160d80836020b418,0xf8183e120dc0a37,0xc583f0b0fc1a3f12,0x81e0287848170605,0x60b094581f0207c4,0x68dc0837060d80a3,0xfc1a3e020f858370,0x5817120fc183f028,0x37068d82c2d1207c,0x83f028f818])
def s89Blob392441 : Nat := (cbits [0xd7e739f33c65febd,0xbdffefffe7ff03e1,0x99be079f0be671cc,0xf9ffc0ffe03ff0f])
def s89Blob392556 : Nat := (cbits [0xa832421105405294,0x200101000060221,0x655a43526d42ccc,0x7082a950426405])
def s89Mask : Nat := 0xc0c03030c0c03030
abbrev s89Goal : Nat := sGoal &&& s89Mask
abbrev s89StockWords : List Nat := [0x8080202080802020,0xc0c00000c0c00000,0xc0003000c0003000,0xc0c0303000000000]
def s89Fact : Nat × List Nat × Nat × Nat := (s89Mask, s89StockWords, 5, s89Goal)
def s89Cuts : List (Nat × List Nat × Nat × Nat) := []
def s89Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[23, 30, 37, 54, 23, 30, 37, 54, 23, 30, 37, 54, 13, 22, 44, 13, 22, 44, 13, 22, 44, 13, 22, 44], rfl⟩
def s89Witnesses := unpackWitnesses s89StockWords [11798, 273925, 539670, 805381]
def s89Index (i : Nat) : Nat := unpack 0x9 2 i
def s89Codes (i : Nat) : Nat := unpack 0xf 15 i
def s89Forest (i : Nat) : Nat := unpack 0x1e 14 i
def s89Links := pageLinks s89Index s89Codes 1 13 1 2
def s89Data (i : Nat) : Nat × Nat :=
  let e := s89Forest i
  (e &&& 1, e >>> 1)
def s89Sample : Nat × Nat := (s89Blob392053, 63)
def s89Tags := dagTraceTags s89Mask 63 (dagTagBases s89StockWords s89Blob392441 s89Blob392556 63) 4 s89Data
def s89States := dagTrace s89Mask s89StockWords 4 s89Data
def s89MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s89Moves := dagMoves s89MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Autos : DagMovesOK s89Mask s89Goal 64 s89Moves := dagMovesOfCheck (by decide +kernel)
def s89Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack 0x0 1 (i % 16)
def s89Check := dagCheckNode s89Mask s89Goal s89Chart (fun i => dagKnownCloses s89Goal (cutPick s89Cuts (s89Choice i))) 1 s89States s89Moves s89Links s89Sample s89Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Roots : dagCheckRoots s89Mask s89Goal s89Chart (dagKnownCloses s89Goal s89Cuts) s89Witnesses (dagRef 1 s89States s89Moves s89Links 0) s89StockWords 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Block0 : treeBlock 0 1 s89Check = true := by decide +kernel
theorem s89Blocks : treeBlock 0 1 s89Check = true := s89Block0
theorem s89Known : Known s89Cuts := (show Known [] from fun _ h => False.elim (List.not_mem_nil h))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s89Stock : Lower s89Mask s89StockWords s89Goal 5 := by
  apply lowerDag s89Choice _ _ _ _ s89Autos _ _ _ s89Known _ s89Roots s89Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s89Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    exact False.elim h
def s90Mask : Nat := 0xcc003300cc003300
abbrev s90Goal : Nat := sGoal &&& s90Mask
abbrev s90StockWords : List Nat := [0x8800220088002200,0xcc000000cc000000,0xc0003000c0003000,0xcc00330000000000]
def s90Fact : Nat × List Nat × Nat × Nat := (s90Mask, s90StockWords, 5, s90Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s90Stock : Lower s90Mask s90StockWords s90Goal 5 := dagShiftLower (width := 64) pm0 s89Stock (by decide +kernel)
def s91Blob396215 : Nat := (cbits [0x78341b0b05c2413,0x4402100884341e0b,0x29048a448250289,0x6190cc582d068b45,0x90e8343a190d82c3,0x4c34130b04c02131,0x121b0905c0a17190,0x1f09078181e0906c,0x84341f0b07c1a,0x844821048840a21,0x41a2502094022514,0x29008a458251009,0xd160a44029068a41,0x20b4182d048b40a2,0xd82436090cc502d1,0x243a190dc2c37120,0x3e190ec343b140e8,0x190f8583e0d0f82c,0x85c12130284c0013,0xc34170685c081700,0xa1b0406c021b1905,0xe02078641b0b06c1,0x9078581e06878101,0x7c181f0487c0a1f1,0x1a21040840821090,0x2500094642116084,0xa450250609412])
def s91Blob396781 : Nat := (cbits [0xccffffff3fc3fe7,0x7fffe01ffffc1fff,0x3ffffffff80000,0xf0f7c1f07cc0d99a,0x7f031e1c783fe0f8,0x803fff00ff07fe00,0xffffffff8003ffe0,0xffc00000])
def s91Blob396966 : Nat := (cbits [0xca5311440aa0,0x6abbe01f110c852e,0x42218c0bdd80000,0x506369653448598a,0x55111e142355ac32,0x7399c6646605ad4a,0xcaa6318c0022b540,0x46031080])
def s91Mask : Nat := 0xcccc3333cccc3333
abbrev s91Goal : Nat := sGoal &&& s91Mask
abbrev s91StockWords : List Nat := [0x8888222288882222,0xcccc0000cccc0000,0xc0c03030c0c03030,0xcc003300cc003300,0xcccc333300000000]
def s91Fact : Nat × List Nat × Nat × Nat := (s91Mask, s91StockWords, 8, s91Goal)
def s91Cuts : List (Nat × List Nat × Nat × Nat) := [s75Fact, s88Fact, s78Fact, s89Fact, s90Fact, s9Fact, s7Fact]
def s91Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[19, 30, 33, 54, 58, 19, 30, 33, 54, 58, 19, 30, 13, 22, 26, 44, 50, 13, 22, 26, 44, 50, 13, 22], rfl⟩
def s91Witnesses := unpackWitnesses s91StockWords [9746, 271873, 539674, 801814, 1065473]
def s91Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x240100400d307001,0x4350140489204810,0x5c9705c1]) else (cbits [0x6d9b06c19264190,0xbc2789c2168421])) 10 (i % 16)
def s91Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x522807410040001f,0xc64b18a14037200,0x14310263334464a7,0x1034c3965870ba4b,0x118701a4b023]) else (if j < 2 then (cbits [0x71324b0761c0c92c,0xb0e2c49618620258,0x2f49620c383d2586,0x104c32908628930e,0x5525979894c3]) else (cbits [0x4030ca4318a2cc38,0x30e154961e625b0c,0x919a8e32910628c,0x962463140c4a6988,0xc30e164]))) 19 (i % 16)
def s91Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x608c4020040403e0,0x9258600e85870249,0x6e161c24052161c1,0x161c30c40c18a040,0x4963c632]) else (cbits [0x985871219285870f,0x5871549654c40119,0x72161c0587184960,0x18])) 18 (i % 16)
def s91Links := pageLinks s91Index s91Codes 4 13 5 5
def s91Data (i : Nat) : Nat × Nat :=
  let e := s91Forest i
  (e &&& 31, e >>> 5)
def s91Sample : Nat × Nat := (s91Blob396215, 96)
def s91Tags := dagTraceTags s91Mask 96 (dagTagBases s91StockWords s91Blob396781 s91Blob396966 96) 7 s91Data
def s91States := dagTrace s91Mask s91StockWords 7 s91Data
def s91MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)))]
def s91Moves := dagMoves s91MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s91Autos : DagMovesOK s91Mask s91Goal 64 s91Moves := dagMovesOfCheck (by decide +kernel)
def s91Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x54000260000022bf,0x188000c2000]) else 0x80220000b0003080) 7 (i % 16)
def s91Check := dagCheckNode s91Mask s91Goal s91Chart (fun i => dagKnownCloses s91Goal (cutPick s91Cuts (s91Choice i))) 27 s91States s91Moves s91Links s91Sample s91Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s91Roots : dagCheckRoots s91Mask s91Goal s91Chart (dagKnownCloses s91Goal s91Cuts) s91Witnesses (dagRef 27 s91States s91Moves s91Links 0) s91StockWords 7 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s91Block0 : treeBlock 0 24 s91Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s91Block24 : treeBlock 24 3 s91Check = true := by decide +kernel
theorem s91Group0_27 : treeBlock 0 27 s91Check = true := treeBlock_merge (start := 0) (left := 24) (right := 3) (check := s91Check) s91Block0 s91Block24
theorem s91Blocks : treeBlock 0 27 s91Check = true := s91Group0_27
theorem s91Known : Known s91Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s7Stock) s9Stock) s90Stock) s89Stock) s78Stock) s88Stock) s75Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s91Stock : Lower s91Mask s91StockWords s91Goal 8 := by
  apply lowerDag s91Choice _ _ _ _ s91Autos _ _ _ s91Known _ s91Roots s91Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s91Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def pm35 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13, st12, st45]
def s92Mask : Nat := 0x3030303003030303
abbrev s92Goal : Nat := sGoal &&& s92Mask
abbrev s92StockWords : List Nat := [0x2020202002020202,0x3030303000000000,0x3000300003000300,0x3030000003030000]
def s92Fact : Nat × List Nat × Nat × Nat := (s92Mask, s92StockWords, 5, s92Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s92Stock : Lower s92Mask s92StockWords s92Goal 5 := dagShiftLower (width := 64) pm35 s75Stock (by decide +kernel)
def s93Blob402839 : Nat := (cbits [0x8542413080440211,0x412190b05c281502,0x81d06874341b0c06,0x10e078341e0b0783,0x20940a2510084022,0xb41a2d140a412291,0x6835190cc6031160,0x391a0d864360b0d8,0x1c0e8643a0d0e870,0xf0683c160f0383c,0x412110284400111c,0x110c04428110904,0x30b04c20130084c6,0x205402151904c341,0x542c15080541a150,0x24170285c68150e0,0x190406402190a05c,0xe0643419080641a,0x6c241b0486c7019,0x4181d048740a1d0c,0x41e06078301d0a07,0xf0687c301e0a0782,0x84381f0d07c2c1,0x844821048840a210,0x825008946021140,0x2516094402506894,0x68a41029008a468])
def s93Blob403407 : Nat := (cbits [0xfffffff011ffc7ff,0xee803924ffffe1ff,0x1fe0e0380f800,0x3ff000f0f333e38,0xf03c3fc01f81fff0,0xe001fffffc00000f,0xffffffffffc03fff,0xffffc0000001ffff,0xfffe00000000000f])
def s93Blob403619 : Nat := (cbits [0x1485086000154249,0x66801924a28c2032,0xc4044110e080,0x92f621270b332e38,0xb03c37c09b156ad0,0xca29b36bd824424b,0xe378f78dffc03db6,0xddea80001041dd8d,0x1c7000010040840e])
def s93Mask : Nat := 0xffff3333ffff3333
abbrev s93Goal : Nat := sGoal &&& s93Mask
abbrev s93StockWords : List Nat := [0xaaaa2222aaaa2222,0xcccc0000cccc0000,0xf0f03030f0f03030,0xff003300ff003300,0xffff0000ffff0000,0xffff333300000000]
def s93Fact : Nat × List Nat × Nat × Nat := (s93Mask, s93StockWords, 10, s93Goal)
def s93Cuts : List (Nat × List Nat × Nat × Nat) := [s91Fact, s66Fact, s16Fact, s43Fact, s44Fact, s92Fact, s26Fact, s45Fact, s9Fact, s70Fact]
def s93Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[17, 30, 33, 54, 58, 60, 17, 30, 33, 54, 58, 60, 13, 22, 26, 28, 44, 50, 52, 56, 13, 22, 26, 28], rfl⟩
def s93Witnesses := unpackWitnesses s93StockWords [8720, 277532, 539674, 801814, 1057281, 1327617]
def s93Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x3c01c10a9c068001,0x8003c21e00f00780,0x3889064232101004,0x2901]) else (if j < 2 then (cbits [0x5412a01484a40520,0xd806a1340988cacc,0xd80e446e23701b04,0x3b01]) else (cbits [0x8a04312181082767,0x404a0050022ad140,0x909480a405202901,0x5402]))) else (if j < 4 then (cbits [0xb095802c01600a84,0x8c8c606303105842,0x501a42d206903389,0x6a0b]) else (if j < 5 then (cbits [0xe62720b885bc4d64,0x40fa47d03e81d50,0x88209f0408204086,0x910c]) else 0x248d240))) 13 (i % 16)
def s93Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 5 then (if j < 2 then (if j < 1 then (cbits [0x848c54046280003f,0xe2c64e2831f0b18d,0x3e3431c19fca0ca,0xb3331397988494c4,0x623990d10c7e7e62,0xa549]) else (cbits [0x63a50f1127f5e92d,0xc08c40a0f454c7a2,0xf0492c0631f82989,0xc087a283bd121927,0xc0224b011e880692,0x8461])) else (if j < 3 then (cbits [0x9252830c5015250,0x40c7c1a62413928,0x1ec380e31008bd1,0xc18c08a4d03d26,0xc0ca528612642a93,0x1a61]) else (if j < 4 then (cbits [0xb24b03463037250,0x3cc481c624177a2,0x82ec3c11312080c6,0x1d19e0f494074c9,0x612192488c904062,0xa049]) else (cbits [0x10a5229129344948,0xc980574292c23310,0x73462b0231013810,0xf2a4969424b080c8,0x296bd10b12865693,0x2e7a])))) else (if j < 7 then (if j < 6 then (cbits [0x224b0a5e880692c,0xc5294609322961c,0xa314329285530e,0x4304961b9928d0c4,0x55830e0f52947093,0xbd62]) else (cbits [0x1b1890d52687d250,0xed27c6a62039192,0x74c38363101e3d1,0x4401981e3100e8c6,0x221c941098947062,0x3931])) else (if j < 8 then (cbits [0x1d9890e926082f44,0x418628789304131e,0x86e63245310090c9,0xab61c1ea4c8c525,0x45624b1206908d25,0x494a]) else (if j < 9 then (cbits [0xa6807d2925896949,0x41cc419c0374e015,0x63662b1331385188,0xd2d4964d98de4cc6,0xc21a4dcf92666492,0xad61]) else (cbits [0x8418813d89164c39,0x1192925c92c1e324,0xc6624d730e]))))) 21 (i % 16)
def s93Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x33100218a0101f80,0x82313827a2034960,0xa817a2827a20231f,0x140c18d819280a18,0x61c0e3100e3120d3]) else (if j < 2 then (cbits [0xc4a50c7a20d31f0d,0x164981518f819280,0x515499157a216496,0x9f819281561c154a,0x1a1819281d3261d1]) else (cbits [0x3324204a42131020,0xa631001324a03102,0x22949626021a6015,0xa1a649fa6496a67a,0x310817a2a67a2264]))) else (if j < 4 then (cbits [0x1928304a53049930,0x3649a35310343138,0x23949a3432534312,0xa23949f3961c3a19,0x31581928344a5347]) else (if j < 5 then (cbits [0x625407a24119840,0x453104531f819284,0x4481a44832181928,0xa2014a4c84964a4a,0x6244f015cd00fcd7]) else 0x7a281))) 20 (i % 16)
def s93Links := pageLinks s93Index s93Codes 5 13 7 6
def s93Data (i : Nat) : Nat × Nat :=
  let e := s93Forest i
  (e &&& 127, e >>> 7)
def s93Sample : Nat × Nat := (s93Blob402839, 96)
def s93Tags := dagTraceTags s93Mask 96 (dagTagBases s93StockWords s93Blob403407 s93Blob403619 96) 9 s93Data
def s93States := dagTrace s93Mask s93StockWords 9 s93Data
def s93MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)))]
def s93Moves := dagMoves s93MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Autos : DagMovesOK s93Mask s93Goal 64 s93Moves := dagMovesOfCheck (by decide +kernel)
def s93Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x100000000773c06,0xcfb380173c0001c0,0x38]) else (if j < 2 then (cbits [0x1384f0030400000,0xce00090000800000,0xf3c0073a]) else (cbits [0x11c000030600060,0x4000000000070000,0xb380001c]))) else (if j < 4 then (cbits [0xf380000000,0x384e4000,0x33800200]) else (if j < 5 then (cbits [0x3ce00000000ce,0x70000091ace9380,0x2]) else 0x3ce))) 10 (i % 16)
def s93Check := dagCheckNode s93Mask s93Goal s93Chart (fun i => dagKnownCloses s93Goal (cutPick s93Cuts (s93Choice i))) 81 s93States s93Moves s93Links s93Sample s93Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Roots : dagCheckRoots s93Mask s93Goal s93Chart (dagKnownCloses s93Goal s93Cuts) s93Witnesses (dagRef 81 s93States s93Moves s93Links 0) s93StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Block0 : treeBlock 0 24 s93Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Block24 : treeBlock 24 24 s93Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Block48 : treeBlock 48 24 s93Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Block72 : treeBlock 72 9 s93Check = true := by decide +kernel
theorem s93Group0_48 : treeBlock 0 48 s93Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s93Check) s93Block0 s93Block24
theorem s93Group48_33 : treeBlock 48 33 s93Check = true := treeBlock_merge (start := 48) (left := 24) (right := 9) (check := s93Check) s93Block48 s93Block72
theorem s93Group0_81 : treeBlock 0 81 s93Check = true := treeBlock_merge (start := 0) (left := 48) (right := 33) (check := s93Check) s93Group0_48 s93Group48_33
theorem s93Blocks : treeBlock 0 81 s93Check = true := s93Group0_81
theorem s93Known : Known s93Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s70Stock) s9Stock) s45Stock) s26Stock) s92Stock) s44Stock) s43Stock) s16Stock) s66Stock) s91Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s93Stock : Lower s93Mask s93StockWords s93Goal 10 := by
  apply lowerDag s93Choice _ _ _ _ s93Autos _ _ _ s93Known _ s93Roots s93Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s93Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s94Blob410320 : Nat := (cbits [0x82c060b0281c0607,0xc2011008441a0f04,0x8150285424130184,0xb0c06412190b05c2,0xb078381d06874341,0x8c02210e078341e0,0x1a2d048a40a25018,0x361a0d46433180c4,0x1c0e46836190d82c,0xf0703a190e8343a,0xc02071c0f0683c0e,0xa0b0082c2c070681,0xf0283c060f0d02c1,0x48440a1101844120,0x4430110a04424110,0x2c130804c0213180,0x150085464130d04c,0xe0542c15080541a,0x5c0a170185c6815,0x41a1900864281709,0x190e06434190806,0xb0906c121b0186c7,0xa074121d02874301,0x78281e09078301d0,0x341f0b07c1a1f0c0,0x210288406210e07c,0x1908c02231808412])
def s94Blob410892 : Nat := (cbits [0xffffffc08ff1ffff,0x742e499fffc7ffff,0xc3f8781e07c07fc7,0xf80071f8794f8e13,0x818ff01c03ff801f,0x3ffffe000007e3f,0xffff803ffe0fffe0,0xfff0000003ffffff,0xfc0000000000003f])
def s94Blob411107 : Nat := (cbits [0x1843f6c001f092bf,0x342649855c419866,0x8588290a47049903,0xd1092598594b8e12,0x818df0180ad28255,0x1365574092124cad,0xe7bc093ffe0f6d40,0xee000000a3be6799,0xa000040104200036])
def s94Mask : Nat := 0xffffaaaaffffaaaa
abbrev s94Goal : Nat := sGoal &&& s94Mask
abbrev s94StockWords : List Nat := [0xaaaaaaaaaaaaaaaa,0xcccc8888cccc8888,0xf0f0a0a0f0f0a0a0,0xff00aa00ff00aa00,0xffff0000ffff0000,0xffffaaaa00000000]
def s94Fact : Nat × List Nat × Nat × Nat := (s94Mask, s94StockWords, 10, s94Goal)
def s94Cuts : List (Nat × List Nat × Nat × Nat) := [s66Fact, s16Fact, s9Fact, s28Fact, s83Fact, s70Fact]
def s94Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 11, 17, 30, 33, 54, 58, 60, 7, 11, 17, 30, 3, 13, 22, 26, 28, 50, 52, 56, 3, 13, 22, 26], rfl⟩
def s94Witnesses := unpackWitnesses s94StockWords [8720, 265733, 527875, 792067, 1057281, 1327617]
def s94Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x4802400abc068001,0x9824c02601300904,0x40ca005002709380,0x2b01]) else (if j < 2 then (cbits [0x6403201618b00561,0xf407813251900c80,0xf84fc07c13e01e84,0x4001]) else (cbits [0x8204102081002800,0x200900480230904a,0x80524e9014802401,0x5102]))) else (if j < 5 then (if j < 4 then (cbits [0xb00570a899440a20,0xa40b4f5a02d01604,0x581ac0d226903481,0x6b03]) else (cbits [0xde06e0b701ac6d60,0xd54ea07503a81bcc,0x102043020800bf85,0x822c])) else (if j < 6 then (cbits [0x1608b045822c10e4,0x5c32648d346062c3,0xd8a6c1341990cc06,0x9d44]) else (cbits [0x540a6253029814a1,0xec3760ba0d542a81,0x31877e7bc1de02])))) 13 (i % 16)
def s94Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0x888c54046280003f,0xe5864e4831f1618d,0x623432c19fd20ca,0xb48313a21884dcc4,0x631190d78c7eac62,0xb749]) else (if j < 2 then (cbits [0x71250f7927f8892d,0xc0803ed6f45657a2,0x20862003021c100a,0xf0a31584189c1cc4,0x6c224b030c861663,0x8749]) else (cbits [0x86bd12312871693f,0x19e880a92c0f7a2,0x81c03d0931204a4d,0x61001e4330e01925,0x609992a48c642462,0x1449]))) else (if j < 4 then (cbits [0xb8c50564a128c38,0x848c403634a19199,0x4409321f4960e98c,0xc239281130e08529,0x80e0040680203003,0x1e49]) else (if j < 5 then (cbits [0x1424c8952603c630,0xae4a054c38294a5,0x84ec3c277a21324b,0x9b1990d8c98b462,0x857b0e0bd2582662,0x3092]) else (cbits [0x9a1920c8c405c03c,0x6d12916492c36324,0x86a620334a45b252,0x3390159c007ecd25,0x38a188410c407404,0xa231])))) else (if j < 9 then (if j < 7 then (cbits [0x19190cbcc7f5462b,0xcf927e7a92d3b496,0x884f45407a21fa50,0xc4101e9e3d101525,0x2180f0f18700c92,0x731]) else (if j < 8 then (cbits [0x232529152643e625,0x4206288f250bd61c,0x140331201928c8c6,0x44549626192924c4,0xa2ac943158709c93,0x4a49]) else (cbits [0x48c513403896624,0x128c40a63254f192,0xa23375018a2a3d1,0x523182930e12cc4,0x8ab8cc028628a8c4,0x5b19]))) else (if j < 11 then (if j < 10 then (cbits [0x2ec941718949c624,0x13cc48b23435818a,0xa2624503122d3d1,0x5a31e29a4c14926,0x28d8c642c628a893,0x2119]) else (cbits [0x2324b130c64be620,0x180078c3250be61c,0x37e92c631a4860c5,0x768015b3007d9129,0x869881a807bd003,0x1531])) else (if j < 12 then (cbits [0xd198ccacc5646627,0xd1d25a8092cab31b,0x380c385d49baaa4c,0xc6962433a5231d87,0xe60bd11058701c92,0x6c01]) else (cbits [0xa124b0c0c921e620,0x38589384c38614a4,0x186c384349608188]))))) 21 (i % 16)
def s94Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x200f8218a0101f80,0x549605310020218,0xa0931382310827a2,0x218231f823158249,0x7a28201e8e7a2023]) else (if j < 2 then (cbits [0x23131218a8101e10,0x8192812496123251,0x91701e1818a1718d,0x81c1a5170081a19,0x496174981e319170]) else (cbits [0x761c174a51749917,0x264982518f819281,0x525499257a226496,0x9f819282561c254a,0x4962d01e2e18a2d1]))) else (if j < 5 then (if j < 4 then (cbits [0x3310321a1819282d,0xb231035324324a43,0x5b800fb831001324,0xa23c49638021b801,0x4a1b849fb8496b87]) else (cbits [0x37a2b801ec17a238,0x45499453108101e4,0x4931381928454a5,0x25493124b49a4a31,0x1924f49a4900e4d3])) else (if j < 6 then (cbits [0xf61c5019bd018a50,0x81928497a24f192c,0x1d818a5819857315,0x2557198d77a2581a,0x3105f31f81928576]) else (cbits [0x3321819285f01e60,0xe67a2014a4e31a4e,0x469015e64a46700f,0x1e6c7a28101ee662])))) 20 (i % 16)
def s94Links := pageLinks s94Index s94Codes 5 13 7 6
def s94Data (i : Nat) : Nat × Nat :=
  let e := s94Forest i
  (e &&& 127, e >>> 7)
def s94Sample : Nat × Nat := (s94Blob410320, 96)
def s94Tags := dagTraceTags s94Mask 96 (dagTagBases s94StockWords s94Blob410892 s94Blob411107 96) 9 s94Data
def s94States := dagTrace s94Mask s94StockWords 9 s94Data
def s94MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)))]
def s94Moves := dagMoves s94MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Autos : DagMovesOK s94Mask s94Goal 64 s94Moves := dagMovesOfCheck (by decide +kernel)
def s94Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 3 then (if j < 1 then (cbits [0x40000000030001c3,0x400c004]) else (if j < 2 then (cbits [0x84003f000041fc0,0x4820044]) else (cbits [0x400003cf041914,0x4003f01]))) else (if j < 5 then (if j < 4 then (cbits [0x2c10270089c1,0x10000c]) else (cbits [0x3f00103f001003,0xcb00500])) else (if j < 6 then (cbits [0x6df000000000,0x3f00104]) else (cbits [0x30000008c006f040,0x3fc])))) 6 (i % 16)
def s94Check := dagCheckNode s94Mask s94Goal s94Chart (fun i => dagKnownCloses s94Goal (cutPick s94Cuts (s94Choice i))) 109 s94States s94Moves s94Links s94Sample s94Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Roots : dagCheckRoots s94Mask s94Goal s94Chart (dagKnownCloses s94Goal s94Cuts) s94Witnesses (dagRef 109 s94States s94Moves s94Links 0) s94StockWords 9 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Block0 : treeBlock 0 24 s94Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Block24 : treeBlock 24 24 s94Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Block48 : treeBlock 48 24 s94Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Block72 : treeBlock 72 24 s94Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Block96 : treeBlock 96 13 s94Check = true := by decide +kernel
theorem s94Group0_48 : treeBlock 0 48 s94Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s94Check) s94Block0 s94Block24
theorem s94Group72_37 : treeBlock 72 37 s94Check = true := treeBlock_merge (start := 72) (left := 24) (right := 13) (check := s94Check) s94Block72 s94Block96
theorem s94Group48_61 : treeBlock 48 61 s94Check = true := treeBlock_merge (start := 48) (left := 24) (right := 37) (check := s94Check) s94Block48 s94Group72_37
theorem s94Group0_109 : treeBlock 0 109 s94Check = true := treeBlock_merge (start := 0) (left := 48) (right := 61) (check := s94Check) s94Group0_48 s94Group48_61
theorem s94Blocks : treeBlock 0 109 s94Check = true := s94Group0_109
theorem s94Known : Known s94Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s70Stock) s83Stock) s28Stock) s9Stock) s16Stock) s66Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s94Stock : Lower s94Mask s94StockWords s94Goal 10 := by
  apply lowerDag s94Choice _ _ _ _ s94Autos _ _ _ s94Known _ s94Roots s94Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s94Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s95Mask : Nat := 0xffffccccffffcccc
abbrev s95Goal : Nat := sGoal &&& s95Mask
abbrev s95StockWords : List Nat := [0xaaaa8888aaaa8888,0xcccccccccccccccc,0xf0f0c0c0f0f0c0c0,0xff00cc00ff00cc00,0xffff0000ffff0000,0xffffcccc00000000]
def s95Fact : Nat × List Nat × Nat × Nat := (s95Mask, s95StockWords, 10, s95Goal)
def s95Witnesses := unpackWitnesses s95StockWords [3590, 277532, 527875, 792067, 1058307, 1328643]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s95Stock : Lower s95Mask s95StockWords s95Goal 10 := by
  apply essentialLift (witnesses := s95Witnesses) (cut := s12Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s12StockWords) (by decide +kernel)
  · exact s12Stock
  · decide +kernel
def s96Mask : Nat := 0xfffff0f0fffff0f0
abbrev s96Goal : Nat := sGoal &&& s96Mask
abbrev s96StockWords : List Nat := [0xaaaaa0a0aaaaa0a0,0xccccc0c0ccccc0c0,0xf0f0f0f0f0f0f0f0,0xff00f000ff00f000,0xffff0000ffff0000,0xfffff0f000000000]
def s96Fact : Nat × List Nat × Nat × Nat := (s96Mask, s96StockWords, 10, s96Goal)
def s96Witnesses := unpackWitnesses s96StockWords [3590, 265733, 539674, 793606, 1059333, 1329669]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s96Stock : Lower s96Mask s96StockWords s96Goal 10 := by
  apply essentialLift (witnesses := s96Witnesses) (cut := s31Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s31StockWords) (by decide +kernel)
  · exact s31Stock
  · decide +kernel
def s97Mask : Nat := 0xffffff00ffffff00
abbrev s97Goal : Nat := sGoal &&& s97Mask
abbrev s97StockWords : List Nat := [0xaaaaaa00aaaaaa00,0xcccccc00cccccc00,0xf0f0f000f0f0f000,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffff0000000000]
def s97Fact : Nat × List Nat × Nat × Nat := (s97Mask, s97StockWords, 10, s97Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s97Stock : Lower s97Mask s97StockWords s97Goal 10 := dagShiftLower (width := 64) pm0 s96Stock (by decide +kernel)
def s98Mask : Nat := 0xffffffff00ff00ff
abbrev s98Goal : Nat := sGoal &&& s98Mask
abbrev s98StockWords : List Nat := [0xaaaaaaaa00aa00aa,0xcccccccc00cc00cc,0xf0f0f0f000f000f0,0xff00ff0000000000,0xffff000000ff0000,0xffffffff00000000]
def s98Fact : Nat × List Nat × Nat × Nat := (s98Mask, s98StockWords, 10, s98Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s98Stock : Lower s98Mask s98StockWords s98Goal 10 := dagShiftLower (width := 64) pm6 s86Stock (by decide +kernel)
def s99Mask : Nat := 0xffffffff0f0f0f0f
abbrev s99Goal : Nat := sGoal &&& s99Mask
abbrev s99StockWords : List Nat := [0xaaaaaaaa0a0a0a0a,0xcccccccc0c0c0c0c,0xf0f0f0f000000000,0xff00ff000f000f00,0xffff00000f0f0000,0xffffffff00000000]
def s99Fact : Nat × List Nat × Nat × Nat := (s99Mask, s99StockWords, 10, s99Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s99Stock : Lower s99Mask s99StockWords s99Goal 10 := dagShiftLower (width := 64) pm9 s86Stock (by decide +kernel)
def s100Mask : Nat := 0xffffffff33333333
abbrev s100Goal : Nat := sGoal &&& s100Mask
abbrev s100StockWords : List Nat := [0xaaaaaaaa22222222,0xcccccccc00000000,0xf0f0f0f030303030,0xff00ff0033003300,0xffff000033330000,0xffffffff00000000]
def s100Fact : Nat × List Nat × Nat × Nat := (s100Mask, s100StockWords, 10, s100Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s100Stock : Lower s100Mask s100StockWords s100Goal 10 := dagShiftLower (width := 64) pm6 s93Stock (by decide +kernel)
def s101Mask : Nat := 0xffffffffaaaaaaaa
abbrev s101Goal : Nat := sGoal &&& s101Mask
abbrev s101StockWords : List Nat := [0xaaaaaaaaaaaaaaaa,0xcccccccc88888888,0xf0f0f0f0a0a0a0a0,0xff00ff00aa00aa00,0xffff0000aaaa0000,0xffffffff00000000]
def s101Fact : Nat × List Nat × Nat × Nat := (s101Mask, s101StockWords, 10, s101Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s101Stock : Lower s101Mask s101StockWords s101Goal 10 := dagShiftLower (width := 64) pm6 s94Stock (by decide +kernel)
def s102Mask : Nat := 0xffffffffcccccccc
abbrev s102Goal : Nat := sGoal &&& s102Mask
abbrev s102StockWords : List Nat := [0xaaaaaaaa88888888,0xcccccccccccccccc,0xf0f0f0f0c0c0c0c0,0xff00ff00cc00cc00,0xffff0000cccc0000,0xffffffff00000000]
def s102Fact : Nat × List Nat × Nat × Nat := (s102Mask, s102StockWords, 10, s102Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s102Stock : Lower s102Mask s102StockWords s102Goal 10 := dagShiftLower (width := 64) pm6 s95Stock (by decide +kernel)
def s103Mask : Nat := 0xfffffffff0f0f0f0
abbrev s103Goal : Nat := sGoal &&& s103Mask
abbrev s103StockWords : List Nat := [0xaaaaaaaaa0a0a0a0,0xccccccccc0c0c0c0,0xf0f0f0f0f0f0f0f0,0xff00ff00f000f000,0xffff0000f0f00000,0xffffffff00000000]
def s103Fact : Nat × List Nat × Nat × Nat := (s103Mask, s103StockWords, 10, s103Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s103Stock : Lower s103Mask s103StockWords s103Goal 10 := dagShiftLower (width := 64) pm6 s96Stock (by decide +kernel)
def s104Mask : Nat := 0xffffffffff00ff00
abbrev s104Goal : Nat := sGoal &&& s104Mask
abbrev s104StockWords : List Nat := [0xaaaaaaaaaa00aa00,0xcccccccccc00cc00,0xf0f0f0f0f000f000,0xff00ff00ff00ff00,0xffff0000ff000000,0xffffffff00000000]
def s104Fact : Nat × List Nat × Nat × Nat := (s104Mask, s104StockWords, 10, s104Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s104Stock : Lower s104Mask s104StockWords s104Goal 10 := dagShiftLower (width := 64) pm9 s96Stock (by decide +kernel)
def s105Mask : Nat := 0xff00ff00ff00ff00
abbrev s105Goal : Nat := sGoal &&& s105Mask
abbrev s105StockWords : List Nat := [0xaa00aa00aa00aa00,0xcc00cc00cc00cc00,0xf000f000f000f000,0xff000000ff000000,0xff00ff0000000000]
def s105Fact : Nat × List Nat × Nat × Nat := (s105Mask, s105StockWords, 9, s105Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s105Stock : Lower s105Mask s105StockWords s105Goal 9 := dagShiftLower (width := 64) pm0 s31Stock (by decide +kernel)
def s106Blob427224 : Nat := (cbits [0x82c0c070281c0607,0x80c0e0502c120b01,0x2110683c180e0503,0x50904c0613080440,0x48642c170a0540a1,0x741a1d0d06c30190,0x381e0d0782c1e0e0,0x230188c402100884,0x1309c48250289444,0xd86835190cc6031,0xc6836190d84c360b,0xa070201c04070081,0xb0082c4c070b01c1,0xd02c1a0b0402c040,0x38100e02038040e0,0x380e0d0382c0e068,0xf0283c060f13038,0x603c140f0483c0c,0x8440a11018440011,0x430110a044241104,0x130104c02131804,0x51904c34130b04c2,0x80541a1502054021,0x5c68150e0542c150,0x24170305c0a17018,0x190406402190a05c,0xe0643419080641a])
def s106Blob427796 : Nat := (cbits [0xfc03ff87fe3ffe3f,0x99c933ffffffffff,0x3e03f00fffffffa,0xfffc1ffce1f1c3c7,0x1fe03f803ffc000,0xfc000000ffffe000,0x7f01fffc00,0xfe000000ffffffff,0x7f])
def s106Blob427991 : Nat := (cbits [0x2c2124802a12561b,0x98c930ed1461410e,0x41a43a1256c6593a,0x9b691e5ce171c346,0x1be03b092dd8824,0xd8091048e1b38400,0x1c2086f01eda800,0xd4000000e31e3cf0,0x10208002001077])
def s106Mask : Nat := 0xff00ffffffffff
abbrev s106Goal : Nat := sGoal &&& s106Mask
abbrev s106StockWords : List Nat := [0xaa00aaaaaaaaaa,0xcc00cccccccccc,0xf000f0f0f0f0f0,0xff00ff00,0xff0000ffff0000,0xff00ff00000000]
def s106Fact : Nat × List Nat × Nat × Nat := (s106Mask, s106StockWords, 9, s106Goal)
def s106Cuts : List (Nat × List Nat × Nat × Nat) := [s37Fact, s40Fact, s2Fact, s24Fact, s36Fact]
def s106Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 11, 14, 17, 33, 54, 7, 11, 14, 17, 33, 54, 3, 13, 22, 26, 28, 38, 50, 52, 3, 13, 22, 26], rfl⟩
def s106Witnesses := unpackWitnesses s106StockWords [3590, 265733, 527875, 792067, 1057281, 1327617]
def s106Index (i : Nat) : Nat := unpack 0x31c30c29301 6 i
def s106Codes (i : Nat) : Nat := unpack (cbits [0x1b980244010003f,0x10c509870ac384]) 17 i
def s106Forest (i : Nat) : Nat := unpack (cbits [0x4961c2004101f8,0x61c101b9]) 16 i
def s106Links := pageLinks s106Index s106Codes 3 13 3 4
def s106Data (i : Nat) : Nat × Nat :=
  let e := s106Forest i
  (e &&& 7, e >>> 3)
def s106Sample : Nat × Nat := (s106Blob427224, 96)
def s106Tags := dagTraceTags s106Mask 96 (dagTagBases s106StockWords s106Blob427796 s106Blob427991 96) 8 s106Data
def s106States := dagTrace s106Mask s106StockWords 8 s106Data
def s106MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := []
def s106Moves := dagMoves s106MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Autos : DagMovesOK s106Mask s106Goal 64 s106Moves := dagMovesOfCheck (by decide +kernel)
def s106Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack 0x1e1001ff 5 (i % 16)
def s106Check := dagCheckNode s106Mask s106Goal s106Chart (fun i => dagKnownCloses s106Goal (cutPick s106Cuts (s106Choice i))) 6 s106States s106Moves s106Links s106Sample s106Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Roots : dagCheckRoots s106Mask s106Goal s106Chart (dagKnownCloses s106Goal s106Cuts) s106Witnesses (dagRef 6 s106States s106Moves s106Links 0) s106StockWords 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Block0 : treeBlock 0 6 s106Check = true := by decide +kernel
theorem s106Blocks : treeBlock 0 6 s106Check = true := s106Block0
theorem s106Known : Known s106Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s36Stock) s24Stock) s2Stock) s40Stock) s37Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s106Stock : Lower s106Mask s106StockWords s106Goal 9 := by
  apply lowerDag s106Choice _ _ _ _ s106Autos _ _ _ s106Known _ s106Roots s106Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s106Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s107Mask : Nat := 0xffffff00ffffff
abbrev s107Goal : Nat := sGoal &&& s107Mask
abbrev s107StockWords : List Nat := [0xaaaaaa00aaaaaa,0xcccccc00cccccc,0xf0f0f000f0f0f0,0xff000000ff00,0xff000000ff0000,0xffffff00000000]
def s107Fact : Nat × List Nat × Nat × Nat := (s107Mask, s107StockWords, 9, s107Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s107Stock : Lower s107Mask s107StockWords s107Goal 9 := dagShiftLower (width := 64) pm6 s106Stock (by decide +kernel)
def s108Mask : Nat := 0xf0f0f0fffffffff
abbrev s108Goal : Nat := sGoal &&& s108Mask
abbrev s108StockWords : List Nat := [0xa0a0a0aaaaaaaaa,0xc0c0c0ccccccccc,0xf0f0f0f0,0xf000f00ff00ff00,0xf0f0000ffff0000,0xf0f0f0f00000000]
def s108Fact : Nat × List Nat × Nat × Nat := (s108Mask, s108StockWords, 9, s108Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s108Stock : Lower s108Mask s108StockWords s108Goal 9 := dagShiftLower (width := 64) pm0 s106Stock (by decide +kernel)
def s109Mask : Nat := 0xf0fffff0f0fffff
abbrev s109Goal : Nat := sGoal &&& s109Mask
abbrev s109StockWords : List Nat := [0xa0aaaaa0a0aaaaa,0xc0ccccc0c0ccccc,0xf0f00000f0f0,0xf00ff000f00ff00,0xf0f00000f0f0000,0xf0fffff00000000]
def s109Fact : Nat × List Nat × Nat × Nat := (s109Mask, s109StockWords, 9, s109Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s109Stock : Lower s109Mask s109StockWords s109Goal 9 := dagShiftLower (width := 64) pm9 s106Stock (by decide +kernel)
def s110Blob432982 : Nat := (cbits [0x82c0c070281c0607,0x80c0e0502c120b01,0x2110683c180e0503,0x90a0540a15080440,0xe0741a1d0c064121,0x8c06231008402210,0x4c27120940a25110,0x2d150ac5029048a4,0x150b84c2e160b41a,0xe46835180c4582e,0x683c160f0383c1c,0x8070101c02071c0f,0xb0082c4c070681c0,0x502c1a0b0402c040,0x38100e02038040e1,0x540e13038380e068,0xf0283c060f16038,0x603c140f0483c0c,0x8440a11018440011,0x460110c044281104,0x150685408150085,0x90086468150e0542,0xe064201906864101,0x74121d0287470190,0x210c074281d060,0x21048840a2101884,0x1808450211208444])
def s110Blob433552 : Nat := (cbits [0xfc03ff0e3ffffe3f,0xc93003ffffffffff,0xffffff01,0xfffc1ff5f1c333c7,0xfe03c3f800f81f80,0xffe000ffffe0f9,0xfe0003fc00,0xfffc000000ffffff,0xff000000000000ff])
def s110Blob433753 : Nat := (cbits [0x2c2129001255561b,0xc93000ed0e18a28e,0x1200000255865200,0x9ae91c7571c33346,0xbe03c3b0246a9b14,0x48b6ca28e37388b9,0x4000de0002a800,0xeda8000080c71c70,0xf0041040038210ef])
def s110Mask : Nat := 0x3333ffff3333ffff
abbrev s110Goal : Nat := sGoal &&& s110Mask
abbrev s110StockWords : List Nat := [0x2222aaaa2222aaaa,0xcccc0000cccc,0x3030f0f03030f0f0,0x3300ff003300ff00,0x3333000033330000,0x3333ffff00000000]
def s110Fact : Nat × List Nat × Nat × Nat := (s110Mask, s110StockWords, 9, s110Goal)
def s110Cuts : List (Nat × List Nat × Nat × Nat) := [s68Fact, s43Fact, s36Fact, s5Fact, s26Fact, s45Fact]
def s110Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 11, 14, 17, 33, 60, 7, 11, 14, 17, 33, 60, 3, 13, 28, 38, 42, 44, 52, 56, 3, 13, 28, 38], rfl⟩
def s110Witnesses := unpackWitnesses s110StockWords [3590, 265733, 527875, 792067, 1057281, 1327617]
def s110Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x44110440c506c01,0x3044910441104411,0x54d504c9]) else (cbits [0x6c1836018060180,0x6d5b])) 10 (i % 16)
def s110Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x363002410040003f,0xc509021900271c0,0x123139c6203066a5,0x1a8400859e889a4b,0x912582188030]) else (cbits [0x105bd1020040af44,0x24b0f18a1af440c0,0x104962831445e888,0x209662014628abd1,0x558708a4b0d3])) 19 (i % 16)
def s110Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0xa8801020040407e0,0x401217a208c40201,0x2810218404e100d8,0x17a23466a17a22c6,0x18a3cc40]) else (cbits [0x604c4e17a23d258f,0x1e8817a250629449])) 18 (i % 16)
def s110Links := pageLinks s110Index s110Codes 4 13 5 5
def s110Data (i : Nat) : Nat × Nat :=
  let e := s110Forest i
  (e &&& 31, e >>> 5)
def s110Sample : Nat × Nat := (s110Blob432982, 96)
def s110Tags := dagTraceTags s110Mask 96 (dagTagBases s110StockWords s110Blob433552 s110Blob433753 96) 8 s110Data
def s110States := dagTrace s110Mask s110StockWords 8 s110Data
def s110MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)))]
def s110Moves := dagMoves s110MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s110Autos : DagMovesOK s110Mask s110Goal 64 s110Moves := dagMovesOfCheck (by decide +kernel)
def s110Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x105080000000007f,0x1103a03]) else 0x1000850000) 6 (i % 16)
def s110Check := dagCheckNode s110Mask s110Goal s110Chart (fun i => dagKnownCloses s110Goal (cutPick s110Cuts (s110Choice i))) 23 s110States s110Moves s110Links s110Sample s110Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s110Roots : dagCheckRoots s110Mask s110Goal s110Chart (dagKnownCloses s110Goal s110Cuts) s110Witnesses (dagRef 23 s110States s110Moves s110Links 0) s110StockWords 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s110Block0 : treeBlock 0 23 s110Check = true := by decide +kernel
theorem s110Blocks : treeBlock 0 23 s110Check = true := s110Block0
theorem s110Known : Known s110Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s45Stock) s26Stock) s5Stock) s36Stock) s43Stock) s68Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s110Stock : Lower s110Mask s110StockWords s110Goal 9 := by
  apply lowerDag s110Choice _ _ _ _ s110Autos _ _ _ s110Known _ s110Roots s110Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s110Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s111Mask : Nat := 0x33333333ffffffff
abbrev s111Goal : Nat := sGoal &&& s111Mask
abbrev s111StockWords : List Nat := [0x22222222aaaaaaaa,0xcccccccc,0x30303030f0f0f0f0,0x33003300ff00ff00,0x33330000ffff0000,0x3333333300000000]
def s111Fact : Nat × List Nat × Nat × Nat := (s111Mask, s111StockWords, 9, s111Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s111Stock : Lower s111Mask s111StockWords s111Goal 9 := dagShiftLower (width := 64) pm6 s110Stock (by decide +kernel)
def pm36 : List (List (Nat × Nat) × List (Nat × Nat)) := [st13, st45]
def s112Mask : Nat := 0x3300330000330033
abbrev s112Goal : Nat := sGoal &&& s112Mask
abbrev s112StockWords : List Nat := [0x2200220000220022,0x3000300000300030,0x3300330000000000,0x3300000000330000]
def s112Fact : Nat × List Nat × Nat × Nat := (s112Mask, s112StockWords, 5, s112Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s112Stock : Lower s112Mask s112StockWords s112Goal 5 := dagShiftLower (width := 64) pm36 s75Stock (by decide +kernel)
def s113Blob438744 : Nat := (cbits [0x8440c070281c0607,0x424130184c201100,0x2190b05c28150285,0x10e0741a1d0c0641,0x108c062310084022,0xa44c27120940a251,0x582d068b45029048,0x361a0d46433180c4,0x1a0d86436130d82c,0xf0583c0e0f07039,0xc04070081c703c1a,0xc070b01c1a070201,0x1028440611000444,0xc044281109044121,0x4c04130084c60110,0x2151904c2c13080,0x15080541a1502054,0x185c68150e0542c,0x5c24170305c0a17,0x41a190406402190a,0xa1d1c06438190806,0xd0a074181d048740,0x2884062100084301,0x8448211108412210,0x4230088c6021140,0x251908c4c231008c,0x100941a250209402])
def s113Blob439316 : Nat := (cbits [0xffffffe10fffffff,0xf4130267ffffffff,0xf80000f80f807e0,0xff0007fef99c3387,0x1e03c00f0007c0f,0x7ff00000001f,0xfffff81ffe003ff8,0xffffc00000007fff,0xffff80000000001f])
def s113Blob439527 : Nat := (cbits [0x8508712000a554ab,0x7413026550870c51,0xd09000690d09640,0x7641278eb99c3386,0x1e03c006412354b,0x40245b6024024117,0x78e7821bde002b50,0xef5a80000840638c,0x8e7802004084041d])
def s113Mask : Nat := 0x33ff33ff33ff33ff
abbrev s113Goal : Nat := sGoal &&& s113Mask
abbrev s113StockWords : List Nat := [0x22aa22aa22aa22aa,0xcc00cc00cc00cc,0x30f030f030f030f0,0x3300330033003300,0x33ff000033ff0000,0x33ff33ff00000000]
def s113Fact : Nat × List Nat × Nat × Nat := (s113Mask, s113StockWords, 9, s113Goal)
def s113Cuts : List (Nat × List Nat × Nat × Nat) := [s40Fact, s2Fact, s24Fact, s43Fact, s77Fact, s112Fact, s45Fact]
def s113Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 17, 33, 54, 60, 7, 17, 33, 54, 60, 7, 17, 3, 13, 22, 28, 38, 44, 50, 52, 56, 3, 13, 22], rfl⟩
def s113Witnesses := unpackWitnesses s113StockWords [3590, 265733, 527875, 817204, 1057281, 1327617]
def s113Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x744101400e207401,0x9060580601806011,0x685a0645]) else (if j < 2 then (cbits [0x2781d1741d06c9b0,0x409024081200801e,0xa027190e]) else 0xc0300b12c0a4e81)) 10 (i % 16)
def s113Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x906009020080003f,0x3f200371c0330a02,0xc3930c382a043260,0x4f4440c4338c3f36,0x84f4404c3848f454]) else (if j < 2 then (cbits [0xe0e9320c00808334,0x4314c3f12c381093,0xc3c16f4c1af4418c,0x4f482263c1e04c16,0x2ec482c648280402]) else (cbits [0x4123350431432035,0x4c3a0351402934f4,0x29160293c63c3ef,0x60353ec3c4204918,0x34f441a335843144]))) 20 (i % 16)
def s113Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x82c3808010080fc0,0x81805208cd04004,0x9870324f864990c0,0x83310c67a616c3f1,0x261e03305e8]) else (if j < 2 then (cbits [0x82f4844c78880dc1,0x485808608101401f,0x406acb0e016242c6,0xaeb0fc161c82f446,0x7a63a63c7806]) else (cbits [0xc6f44040930b10c1,0x3d14101a]))) 19 (i % 16)
def s113Links := pageLinks s113Index s113Codes 4 13 6 5
def s113Data (i : Nat) : Nat × Nat :=
  let e := s113Forest i
  (e &&& 63, e >>> 6)
def s113Sample : Nat × Nat := (s113Blob438744, 96)
def s113Tags := dagTraceTags s113Mask 96 (dagTagBases s113StockWords s113Blob439316 s113Blob439527 96) 8 s113Data
def s113States := dagTrace s113Mask s113StockWords 8 s113Data
def s113MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)))]
def s113Moves := dagMoves s113MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s113Autos : DagMovesOK s113Mask s113Goal 64 s113Moves := dagMovesOfCheck (by decide +kernel)
def s113Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 1 then (cbits [0x204023000200387,0x11800000000]) else (if j < 2 then (cbits [0x700004808c00009,0x122000]) else 0x21001c001)) 7 (i % 16)
def s113Check := dagCheckNode s113Mask s113Goal s113Chart (fun i => dagKnownCloses s113Goal (cutPick s113Cuts (s113Choice i))) 37 s113States s113Moves s113Links s113Sample s113Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s113Roots : dagCheckRoots s113Mask s113Goal s113Chart (dagKnownCloses s113Goal s113Cuts) s113Witnesses (dagRef 37 s113States s113Moves s113Links 0) s113StockWords 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s113Block0 : treeBlock 0 24 s113Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s113Block24 : treeBlock 24 13 s113Check = true := by decide +kernel
theorem s113Group0_37 : treeBlock 0 37 s113Check = true := treeBlock_merge (start := 0) (left := 24) (right := 13) (check := s113Check) s113Block0 s113Block24
theorem s113Blocks : treeBlock 0 37 s113Check = true := s113Group0_37
theorem s113Known : Known s113Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s45Stock) s112Stock) s77Stock) s43Stock) s24Stock) s2Stock) s40Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s113Stock : Lower s113Mask s113StockWords s113Goal 9 := by
  apply lowerDag s113Choice _ _ _ _ s113Autos _ _ _ s113Known _ s113Roots s113Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s113Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
def s114Mask : Nat := 0x3f3f3f3f3f3f3f3f
abbrev s114Goal : Nat := sGoal &&& s114Mask
abbrev s114StockWords : List Nat := [0x2a2a2a2a2a2a2a2a,0xc0c0c0c0c0c0c0c,0x3030303030303030,0x3f003f003f003f00,0x3f3f00003f3f0000,0x3f3f3f3f00000000]
def s114Fact : Nat × List Nat × Nat × Nat := (s114Mask, s114StockWords, 9, s114Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s114Stock : Lower s114Mask s114StockWords s114Goal 9 := dagShiftLower (width := 64) pm0 s113Stock (by decide +kernel)
def s115Blob445350 : Nat := (cbits [0x82c060b0281c0607,0xc2011008441a0f04,0x2190a0540a150184,0x10e0741a1d0c0641,0x2894062310084022,0xb45029048a448250,0x6835180c4582d068,0x3c160f0383c1c0e4,0x201c02071c0f068,0x82c100b0082c1a07,0xc120f0283c060f06,0xa110184400110603,0x10c0442811048440,0x85420130084c601,0x5420150685408150,0xa170185c68150e0,0x190406402190a05c,0x1c0643819080641a,0x874301b0486c061b,0x4281d06074121d02,0x210e07c1a1f0c07,0x1048840a21018840,0x88c602114084482,0x9408250089440230,0x6825160944025068,0x291209c0a270189c,0x100a41a29040a402])
def s115Blob445922 : Nat := (cbits [0xffffffffc3ffffff,0xc001009fffffffff,0xe060307038180ff,0x3fe00f1fd663313,0x3e783c1c0ff803f8,0xf00003fffc0000fe,0xffffff003f803fe0,0x3fffc000000003ff,0xfffffc0000000000])
def s115Blob446137 : Nat := (cbits [0x158a8e7b402b55bf,0x10085562a391b,0x200080100800210,0x536c14a99d663312,0x2e783c184db05368,0x60a0a3b6d82828cd,0xe271700037802a40,0x3bd48000010102c4,0x89c5c00080404000])
def s115Mask : Nat := 0xbbbbbbbbbbbbbbbb
abbrev s115Goal : Nat := sGoal &&& s115Mask
abbrev s115StockWords : List Nat := [0xaaaaaaaaaaaaaaaa,0x8888888888888888,0xb0b0b0b0b0b0b0b0,0xbb00bb00bb00bb00,0xbbbb0000bbbb0000,0xbbbbbbbb00000000]
def s115Fact : Nat × List Nat × Nat × Nat := (s115Mask, s115StockWords, 9, s115Goal)
def s115Cuts : List (Nat × List Nat × Nat × Nat) := [s18Fact, s43Fact, s26Fact, s45Fact]
def s115Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 11, 17, 33, 60, 7, 11, 17, 33, 60, 7, 11, 3, 13, 28, 44, 52, 56, 3, 13, 28, 44, 52, 56], rfl⟩
def s115Witnesses := unpackWitnesses s115StockWords [8720, 265733, 527875, 792067, 1057281, 1327617]
def s115Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x4202100d98074001,0x8444202101080840,0x4009464812401184,0x2801]) else (cbits [0x5c02b19504a04500,0xc166002e11700b80,0xe00f007803b09d80,0x3c01])) else (if j < 3 then (cbits [0x7c03e01e08f00780,0x1808064002000f84,0x4811868c04602301,0x4912]) else (if j < 4 then (cbits [0x9e14c1a5852c0960,0x644ac35602b0140c,0x1d7c2b835b0ad81,0x6703]) else (cbits [0xda06c0b4119c2ce0,0xecef41714b881b48,0x4105])))) 13 (i % 16)
def s115Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0xa0090080200003f,0x400cc0e02703006c,0x40430800fc180370,0x8cdc303360b0c502,0x620120d0d3034210,0x15989c4e]) else (cbits [0x6892c1918fc58633,0xeb0e07693f1ba4cc,0xcc4320b0fc80c391,0xcd892f45243d108,0x92c0198810434201,0x230e206])) else (if j < 3 then (cbits [0x1664004813108f44,0x698f014040050cd0,0x204007bd201c93c0,0x9921143404599302,0xc380ab1202894809,0x4bbd102e]) else (cbits [0x3231405809404008,0xd18ca326200d0cc8,0xcc380ea5083892c8,0x98c040f440fb1083,0x64811a4f04463c0d,0x1325204a]))) else (if j < 6 then (if j < 5 then (cbits [0x326420c98d806314,0x53d1052c381424b1,0x2f4e1719285a31c1,0x18f060f4c178c706,0xf4d1718f95a31c18,0x1818f066]) else (cbits [0x326428c98da06314,0xb3d106ac381424b3,0x4f4e1c252a5a3281,0xa4f072f4c978ca07,0xf4d1c24fb5a3281c,0x1ca4f078])) else (if j < 7 then (cbits [0x2e620020c507c019,0xab0e05292c501908,0x43340e19007ef441,0x3d30709311718c48,0x3342280f08694022,0x1818c486]) else (if j < 8 then (cbits [0x3a33423812072931,0x898c43e34c4e8d00,0x893d1d24c46663d1,0x648ac3c2230f07,0x6424b9881083145f,0x1524b040]) else (cbits [0x3864c1fbd106cc38,0x1]))))) 22 (i % 16)
def s115Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0x219b020040101f80,0x810048161c023100,0x609019810138100d,0x1b813200919a0a02,0x7a40d49e0d31e0d0]) else (cbits [0x3021810201101f81,0x1624134a4133241,0xa1919b0161c1718a,0x96193181b1991918,0x6211961c194a1194])) else (if j < 3 then (cbits [0x231e2219b817a219,0x25324251a18149e2,0xc2849628310014a4,0x1981313817a22861,0x18e2f3252d18e2d3]) else (if j < 4 then (cbits [0x331f817a72d7a62f,0x3561c35496017a6b,0x6394a538499817a2,0xa6bc49f817a7387a,0x7a23e00cbe61c017]) else (cbits [0x319a4261f8161c81,0x8101e457a6424a04,0x2817a20102447621,0x7a])))) 20 (i % 16)
def s115Links := pageLinks s115Index s115Codes 5 13 7 6
def s115Data (i : Nat) : Nat × Nat :=
  let e := s115Forest i
  (e &&& 127, e >>> 7)
def s115Sample : Nat × Nat := (s115Blob445350, 96)
def s115Tags := dagTraceTags s115Mask 96 (dagTagBases s115StockWords s115Blob445922 s115Blob446137 96) 8 s115Data
def s115States := dagTrace s115Mask s115StockWords 8 s115Data
def s115MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val))), (pm9, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 5, 4] 0 i.val)))]
def s115Moves := dagMoves s115MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s115Autos : DagMovesOK s115Mask s115Goal 64 s115Moves := dagMovesOfCheck (by decide +kernel)
def s115Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then 0xc00d4810001e else 0x1000000d0f00000d) else (if j < 3 then 0x400050000000 else (if j < 4 then 0x10000000090000 else 0x2110000002))) 4 (i % 16)
def s115Check := dagCheckNode s115Mask s115Goal s115Chart (fun i => dagKnownCloses s115Goal (cutPick s115Cuts (s115Choice i))) 74 s115States s115Moves s115Links s115Sample s115Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s115Roots : dagCheckRoots s115Mask s115Goal s115Chart (dagKnownCloses s115Goal s115Cuts) s115Witnesses (dagRef 74 s115States s115Moves s115Links 0) s115StockWords 8 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s115Block0 : treeBlock 0 24 s115Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s115Block24 : treeBlock 24 24 s115Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s115Block48 : treeBlock 48 24 s115Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s115Block72 : treeBlock 72 2 s115Check = true := by decide +kernel
theorem s115Group0_48 : treeBlock 0 48 s115Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s115Check) s115Block0 s115Block24
theorem s115Group48_26 : treeBlock 48 26 s115Check = true := treeBlock_merge (start := 48) (left := 24) (right := 2) (check := s115Check) s115Block48 s115Block72
theorem s115Group0_74 : treeBlock 0 74 s115Check = true := treeBlock_merge (start := 0) (left := 48) (right := 26) (check := s115Check) s115Group0_48 s115Group48_26
theorem s115Blocks : treeBlock 0 74 s115Check = true := s115Group0_74
theorem s115Known : Known s115Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s45Stock) s26Stock) s43Stock) s18Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s115Stock : Lower s115Mask s115StockWords s115Goal 9 := by
  apply lowerDag s115Choice _ _ _ _ s115Autos _ _ _ s115Known _ s115Roots s115Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s115Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl <;> decide +kernel
def s116Mask : Nat := 0xffffffffffff0000
abbrev s116Goal : Nat := sGoal &&& s116Mask
abbrev s116StockWords : List Nat := [0xaaaaaaaaaaaa0000,0xcccccccccccc0000,0xf0f0f0f0f0f00000,0xff00ff00ff000000,0xffff0000ffff0000,0xffffffff00000000]
def s116Fact : Nat × List Nat × Nat × Nat := (s116Mask, s116StockWords, 9, s116Goal)
def s116Witnesses := unpackWitnesses s116StockWords [8720, 277532, 539674, 801814, 1076262, 1338390]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s116Stock : Lower s116Mask s116StockWords s116Goal 9 := by
  apply essentialLift (witnesses := s116Witnesses) (cut := s16Mask)
  · unfold properWord; decide +kernel
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · unfold properWord; decide +kernel
  · exact suppliesOfCheck (old := s16StockWords) (by decide +kernel)
  · exact s16Stock
  · decide +kernel
def s117Mask : Nat := 0xf0f0f0f0f0f0f0f
abbrev s117Goal : Nat := sGoal &&& s117Mask
abbrev s117StockWords : List Nat := [0xa0a0a0a0a0a0a0a,0xc0c0c0c0c0c0c0c,0xf000f000f000f00,0xf0f00000f0f0000,0xf0f0f0f00000000]
def s117Fact : Nat × List Nat × Nat × Nat := (s117Mask, s117StockWords, 7, s117Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s117Stock : Lower s117Mask s117StockWords s117Goal 7 := dagShiftLower (width := 64) pm0 s40Stock (by decide +kernel)
def s118Mask : Nat := 0xf000f000f000f00
abbrev s118Goal : Nat := sGoal &&& s118Mask
abbrev s118StockWords : List Nat := [0xa000a000a000a00,0xc000c000c000c00,0xf0000000f000000,0xf000f0000000000]
def s118Fact : Nat × List Nat × Nat × Nat := (s118Mask, s118StockWords, 6, s118Goal)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s118Stock : Lower s118Mask s118StockWords s118Goal 6 := dagShiftLower (width := 64) pm17 s2Stock (by decide +kernel)
def s119Blob467735 : Nat := (cbits [0x82c0c070281c0607,0x80c0e0502c120b01,0x2110683c180e0503,0x50904c0613080440,0x48642c170a0540a1,0x741a1d0d06c30190,0x381e0d0782c1e0e0,0x230188c402100884,0x1309c48250289444,0x8b4542b140a41229,0x8542e130b8582d06,0x835190cc6031160b,0x6190d84c360b0d86,0x50e8343a1c0e4683,0xf0383c1c0e8643a1,0x2071c0f0683c160,0x70681c08070101c,0x102c020b1301c2c,0x2c340b0682c100b,0x8100e02038040e15,0x80e0d0382c0e0683,0xf16038540e130383,0x483c0c0f0283c060,0x4400110603c140f0,0x2411048440a11018,0x131804430110a044,0xb04c20130104c02])
def s119Blob468307 : Nat := (cbits [0xff00871ffe3ffe3f,0x99c933ffffffc00f,0xf00fffffff0f7ae4,0x3ff07cf8e1f1c3c7,0x1fe03f8000ffff0,0xfffffc0ff80ff,0xffff0001fffc00,0xfe000000fff00000,0xffffff])
def s119Blob468508 : Nat := (cbits [0x490000092a12561b,0x98c930ed10e2c082,0xa1255b1cb2073a64,0x3c705cb8e171c346,0x1be03b08249ada2,0x48e36cf08bb80df,0x10ddef0001eda800,0xd4000000cf000704,0x800380820eef7f6])
def s119Mask : Nat := 0xffffffffffffffff
abbrev s119Goal : Nat := sGoal &&& s119Mask
abbrev s119StockWords : List Nat := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
def s119Cuts : List (Nat × List Nat × Nat × Nat) := [s23Fact, s34Fact, s35Fact, s38Fact, s39Fact, s41Fact, s42Fact, s46Fact, s47Fact, s48Fact, s49Fact, s50Fact, s51Fact, s52Fact, s53Fact, s54Fact, s55Fact, s56Fact, s57Fact, s58Fact, s59Fact, s60Fact, s61Fact, s62Fact, s63Fact, s64Fact, s72Fact, s86Fact, s87Fact, s93Fact, s94Fact, s95Fact, s96Fact, s97Fact, s71Fact, s98Fact, s99Fact, s100Fact, s101Fact, s102Fact, s103Fact, s104Fact, s12Fact, s31Fact, s105Fact, s106Fact, s107Fact, s108Fact, s109Fact, s111Fact, s110Fact, s113Fact, s114Fact, s115Fact, s116Fact, s17Fact, s66Fact, s67Fact, s16Fact, s20Fact, s1Fact, s37Fact, s68Fact, s40Fact, s117Fact, s2Fact, s24Fact, s118Fact, s43Fact, s36Fact, s8Fact, s21Fact, s9Fact, s27Fact, s28Fact, s83Fact, s70Fact]
def s119Chart : Option ({rows : List Nat // rows.length = 24}) := some ⟨[7, 11, 14, 17, 33, 54, 58, 60, 7, 11, 14, 17, 3, 13, 22, 26, 28, 38, 42, 44, 50, 52, 56, 3], rfl⟩
def s119Witnesses := unpackWitnesses s119StockWords [3590, 265733, 527875, 792067, 1057281, 1327617]
def s119Index (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0x4e302b200340001,0x565056005600541,0x620062006010600,0x7c7064c06210620]) else (if j < 2 then (cbits [0x8e208e008e008a2,0x960092209200920,0xa6209a609a00962,0xc830b0c0b000aa3]) else (cbits [0xd430d210d200ce2,0xde20de00dc10da1,0xe450e400e210e20,0xf060f000ee10ee0]))) else (if j < 4 then (cbits [0x1001100010000fc2,0x1042104010211020,0x132012e21207108c,0x1366136013221320]) else (if j < 5 then (cbits [0x14cb14c014631422,0x1685168016801623,0x1747174017211720,0x18aa184318401821]) else (cbits [0x1be61b831aa719e6,0x1d211d201d011ca3,0x1de01dc11d441d40,0x1e221e201e011de1])))) else (if j < 9 then (if j < 7 then (cbits [0x1f011ea31e811e61,0x206020601fe41f26,0x24a223a8224b206f,0x24e024e024e024e0]) else (if j < 8 then (cbits [0x25602560256024e4,0x2644264026022565,0x2780278026c626c0,0x294028c427a92781]) else (cbits [0x29a029a029432940,0x29c729c029c029a1,0x2b012b002b002aa3,0x2b642b602b222b20]))) else (if j < 10 then (cbits [0x2d802ce52be82be0,0x2fa02f432e0a2d84,0x314030e32fc92fa1,0x321031a331433140]) else (if j < 11 then (cbits [0x35e035e03583340c,0x35e435e035e035e0,0x3683368036613660,0x3709370036e136e0]) else (cbits [0x39e039e039453829,0x3a603a033a0039e1,0x3ac03aa13a623a60,0x3b623b413b213ac3]))))) else (if j < 18 then (if j < 15 then (if j < 13 then (cbits [0x3d263bea3bc13ba1,0x3e613e223e013de1,0x3f433f213f013e84,0x40a240053fe13fa2]) else (if j < 14 then (cbits [0x410040e140e040e0,0x4283416941604103,0x430042e142e042e0,0x43e243c143064300]) else (cbits [0x4449442144204420,0x4720462846014565,0x494049214885472b,0x4982498049614941]))) else (if j < 16 then (cbits [0x4b6a4a2a49c349c0,0x4d004d004d004ca3,0x4d604d604d034d00,0x4da04d814d804d61]) else (if j < 17 then (cbits [0x4f604ee44e074da3,0x4f824f804f614f60,0x504650404fc44fc0,0x5160516051225101]) else (cbits [0x5242522151855161,0x5402534653025284,0x58225785562b544f,0x58e658e058645860])))) else (if j < 21 then (if j < 19 then (cbits [0x59c759a159a059a0,0x5b025b005b005aa3,0x5bc85bc05b445b40,0x5dea5d645d605cc5]) else (if j < 20 then (cbits [0x5fa95f815f805f23,0x61236120612060c3,0x65c0642d61f26183,0x66a06681668065c6]) else (cbits [0x68026746674066a5,0x6900690068466840,0x6a22692869206901,0x6a606a606a606a60]))) else (if j < 23 then (if j < 22 then (cbits [0x6c006a8c6a806a61,0x6da06cc76cc06c06,0x702070016f466dad,0x7084708070427021]) else (cbits [0x73c473c0726b710b,0x7441744074407440,0x758274e574647460,0x77a376c7766375c5])) else (if j < 24 then (cbits [0x7ae97a837988780c,0x7f247ec37de77c0f,0x82e18264812a7fac,0x840983a383818304]) else 0x8646856785608522))))) 16 (i % 16)
def s119Codes (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 34 then (if j < 17 then (if j < 8 then (if j < 4 then (if j < 2 then (if j < 1 then (cbits [0x400900200800003f,0x2713c31b0ce3140a,0x5e233f1e233393c3,0xe63327062722e620,0x33a2e92c6be63f2b,0x2dec38ebe93fabe9]) else (cbits [0x4c432eec3f2e6c39,0xf6e6f456def4430,0x80c02700c01b0040,0xa32703a31b01a314,0x2045c33f05c33383,0x9463308462706e6])) else (if j < 3 then (cbits [0x493386e92c49463f,0x3f09cc38c9493f89,0x692c49cf440a0c,0x8c38806c3800a933,0x2501062000e03200,0x18c380166330146]) else (cbits [0x31b01292c012c38,0x2701c62081032701,0x42e63f02e63302a6,0xe93f82e93381c92c,0x44036c3f032c38c2,0x1e92c812627432f]))) else (if j < 6 then (if j < 5 then (cbits [0x4c3842293f022933,0x38424f44028c3f02,0x20c38420f44020c,0xd25002cf44026f44,0x2c031250822c3842,0x43093f02c9330249]) else (cbits [0x4f44c30c3f824c38,0x20826f44026c3803,0x38c3882892c0286,0xc632816033014025,0x4a04893e04493203,0x50c3f04cc384489])) else (if j < 7 then (cbits [0x8f4b054f44450c4b,0x4403e93045525005,0x40c38443250042f,0xe630040c3c440f44,0x3c447250046f4403,0x4ef4404b2500409]) else (cbits [0x293e05233444f250,0x4444ac4a046c3e04,0x5a34005725004ef,0x894b06493305e92c,0x50868c4b85ec3806,0x63250060c3806d2])))) else (if j < 12 then (if j < 10 then (if j < 9 then (cbits [0x2c3806a328066328,0x2700631b862f4406,0x84c62701c6208183,0x92c45e63f05e633,0x3847893f07893307,0x47cf44080c3f07cc]) else (cbits [0x93301e92c008627,0x3f072c3846093f06,0x20c38472f44076c,0xb250022620074f44,0x3f84e93302492c07,0x47ac3f072c384629])) else (if j < 11 then (cbits [0x4f44026c3807ef44,0x3807692c02862007,0xe01900a00f082c,0x433104432502a314,0x2046434b06433f84,0x90f4b08cf440866]) else (cbits [0xaf4408800e48d250,0x3102c62048b25008,0x8a92c84663d0466,0xe31409264008f250,0x4b85033304832502,0x96c4b878c384683]))) else (if j < 14 then (if j < 13 then (cbits [0x62009863409b250,0x2087af4404a63103,0x8546330546270326,0xc93307c92c46c63f,0x3f87cc3849a93f08,0x3492c09ef44c9ac]) else (cbits [0xec3885693f056933,0x1487ef4408ec3f07,0x85832705831b0363,0x92c090627080620,0x2c0386200a2c3888,0xa6620882c380829])) else (if j < 15 then (cbits [0x292c8b06330b0627,0x2c8c2c380c69330c,0x8a8c380ac9330a89,0x231c0ae6280aac38,0x440bcc3e0b693e0b,0xb8c3c0b4c380c0f]) else (if j < 16 then (cbits [0x893c0be3340ba334,0x2c0b46280ba6300b,0xc4c388c09330a89,0xa32a0c83280aac38,0x3d0bc6310ac6200c,0xae3140cc92c8bc6]) else (cbits [0x892c8be3310be319,0x200a631501a31408,0x10c6330f86270d06,0xc9338d092c50c63f,0x39120c38d0c93f90,0x13ac43130c3f128c])))))) else (if j < 25 then (if j < 21 then (if j < 19 then (if j < 18 then (cbits [0xc620528f45520f44,0x330d292c0a862101,0xe6c384de93f0de9,0x6c430f0c3f0ecc39,0x2c4ecf454e6f440f,0xd4c380aa92d01e9]) else (cbits [0xcc430dac3f0d8c39,0x384d8f454d4f440d,0x226200d6f44020c,0x52500e2f440e0629,0x3f0d4c3802492c0e,0xeaf450e8f444e4c])) else (if j < 20 then (cbits [0x8c380d6f44026c38,0x500eef4a0e2c3d0d,0xf26350286204eb2,0xef440f4c380da92c,0x140dc92c4ef2500e,0xfa31d0ac31502a3]) else (cbits [0x6f4b104f45100f44,0x5150125010af4f10,0xfc92c0ae3145052,0xc6204ff2500fef44,0x401032500fe62902,0x10e31d02e3141086]))) else (if j < 23 then (if j < 22 then (cbits [0x8f44114c4b8dec38,0x2c11f25111d25011,0x1132508e0c381109,0xb2508e2f44116634,0x4411262903062011,0x3262011b2508e4f]) else (cbits [0xc93f1009330e692c,0x44d1cc3f8e6c3851,0x124013126f45122f,0x2c3f0e8c3803492c,0x490eac388e8f4410,0xd1af498eaf4451ac])) else (if j < 24 then (cbits [0x893d1049330ec92c,0x3d8ecc3851e94b11,0x12af4ad1ec4b918c,0xe92c12f251527250,0x5412d2508eec380e,0x13233503631412d2]) else (cbits [0x66270f0620136337,0x44138c388f092c10,0xf262052b25012af,0x8620134f448f292c,0x208f4c380f492c03,0x8f692c10a6270f66])))) else (if j < 29 then (if j < 27 then (if j < 26 then (cbits [0xe0110b000903a008,0x3e18293215c63213,0x1aac3859a94a19a9,0x4f445b8c4b1b8c3f,0x4f1cef4b1caf451c,0x5cb2515c52501e0f]) else (cbits [0x66211406200b2008,0x4b14a63f14863314,0x150c3f14cc3854a6,0x8f4b154f44550c4b,0x44142c3855525015,0xb4314545250144f])) else (if j < 28 then (cbits [0xf25014ef4414292c,0x4414492c15203454,0x15a04015725014ef,0xe9300b600903c008,0x4b17af45176f4415,0x577250180f4f17cf]) else (cbits [0x800903e00857b251,0x3916ac381600290b,0x174c43170c3f16ec,0xa00856ef4556af44,0x3f164c3816292c0b,0x168034564f44166c]))) else (if j < 31 then (if j < 30 then (cbits [0xcf44164335040314,0x2817203516602916,0x16ac3c0423141680,0xec3c16cf48179250,0x3017093017e04116,0x440081749301729]) else (cbits [0xe6301840290bc009,0x4b192f4518ef4415,0x58f250198f4f194f,0x6300be008593251,0x4b188f4418692c16,0x16293058925018af])) else (if j < 32 then (cbits [0x663018c04016493c,0x3504631416832416,0x19125016a93c1883,0xa02916e93c16cc48,0x2817063019604118,0x17463017263018c0]) else (if j < 33 then (cbits [0x2f4419c029048008,0x2c1a92511a72501a,0x1a52501a125019e9,0x52501a033504a314,0x1d0c031504c3141a,0x1b0f451acf4414c3]) else (cbits [0xd2501b6f4f1b2f4b,0x2904e6205b12515a,0x1b46401af25014e6,0xa035150011050008,0x5c1c12501bc3341b,0x520081520101c35]))))))) else (if j < 51 then (if j < 42 then (if j < 38 then (if j < 36 then (if j < 35 then (cbits [0x43141be6401bf250,0x3e17693e15431d05,0x1acf445a6c4a18ec,0x92511c72505c2f4b,0x4a1566290566201c,0x1af250190f4a178c]) else (cbits [0x2c3e17a93e5a4f54,0x445a8c561a2c4819,0x1cd2561c0f491b0f,0x80110580085c955c,0x401d80431d004115,0x19493217c6321dc3])) else (if j < 37 then (cbits [0xd2501def441b2c38,0x3215a0105cd55c1c,0x1969321d264a17e6,0x46481d49481d694a,0x2c05a0081da6541d,0x1989321806321b49]) else (cbits [0x401105c0081b6c38,0x4b21493320092c1e,0xa20c4ba00c382209,0xd25122b250226f44,0x331ec6271e662022,0x1f092c1ee64b9ec6]))) else (if j < 40 then (if j < 39 then (cbits [0xc381fa94b1f6933,0x2c1ff2509fac4b9f,0x1eb2509e8c381e89,0x52501f2c381e892c,0x2c1fc0281f80281f,0x9f4f441f4c381ea9]) else (cbits [0x2c381f031d05e314,0x5020cf44208c4b20,0x606202132512112,0x7250204f441f2629,0x50204f4420a63420,0x1f462906262020f2])) else (if j < 41 then (cbits [0x400820f250206f44,0x282160291f601106,0x21f55c21d2502183,0xb2500660081f8010,0x1106800821a63421,0x2243282220291fa0]) else (cbits [0xa0081fc010a08f44,0x3f20cc38a0ac3806,0x229250a0cf4421cc,0xc314a0f25020ef44,0x3f210c381fe31d06,0x229250a10f4421ec])))) else (if j < 46 then (if j < 44 then (if j < 43 then (cbits [0xe314a12f44212c38,0x270d06200c231506,0x60063f2006339aa6,0x493f24493323092c,0x3f25cc39254c3864,0x654f4426ec43264c]) else (cbits [0x462107062065cf45,0x3f2029330d292c0c,0x238c39232c386029,0x2f44242c4323cc3f,0x3807292c638f4563,0x234f44606c3f0d4c])) else (if j < 45 then (cbits [0x6f44074c38236f45,0x4a204c3d0d8c380d,0x7662063725023af,0xc380da92c23e635,0x2c63b25023af4424,0x2463290783140dc9]) else (cbits [0xcf4460864b0de620,0x2025325125125024,0x24b250248c380e06,0xa62024f2500e292c,0x500e492c24a63507,0xe692c07c62024f2]))) else (if j < 48 then (if j < 47 then (cbits [0x2c3861093f9ac933,0x45256f44650c3f23,0x7e92c25801325af,0x4f449aec3f0e8c38,0x4460ec490eac3823,0xec92c64ef49236f]) else (cbits [0x294b20c93d9b0933,0x4b24cc3d238c3861,0x65b25025ef4a652c,0xac380ee92c263251,0x1426125426125023,0x26a3372663350803])) else (if j < 49 then (cbits [0xc92c9b26270f0620,0x5025ef4426cc3823,0x23e92c0f262065f2,0x492c082620268f44,0x270f6620240c380f,0x8400824292c9b66]) else (if j < 50 then (cbits [0x801f27201d0c6009,0x311823250f831428,0x61434b21433f9823,0xe64f29e643292620,0x4b2aaf452a2f4469,0x6a32502bcf4f2aef]) else (cbits [0xa3140c80086ab251,0x312743271843190f,0x61634b21633f9843,0xa94b27a93f27692c,0x50282f4b27ef4467,0xfc62008831467f2])))))) else (if j < 59 then (if j < 55 then (if j < 53 then (if j < 52 then (cbits [0x8f44986631186625,0x2027d25667925027,0x98863d1886250fe6,0x4040281250278c38,0x3118a31928604228,0x67c95527c94998a3]) else (cbits [0xa00898c02518c00d,0x5068ac5628ac4a0c,0x68d55c28f25728d2,0xc31508631429004c,0x4b298f45294f440c,0x69525029cf4f29af])) else (if j < 54 then (cbits [0x725008a620699251,0x142a402b2a155c29,0x28c32b27e32908c3,0xe63d18e631100620,0x4f29492c61e64b98,0x2a92512a72506a09]) else (cbits [0x292c28063508e620,0x3899094919093d10,0x192631104620296c,0x892c21c64999263d,0x86a955c2ad25629,0x28e01f28201d0900]))) else (if j < 57 then (if j < 56 then (cbits [0x63142b60432b0041,0x2099433119432510,0x2baf442b864029a6,0x401c6ad55c2ad250,0x3119632529001e28,0xab2c4a2b294a9963]) else (cbits [0x200828601c2b4c48,0x2510a31410831409,0x29c6209983311983,0xc3142c001d094008,0x4b9b833319a32510,0x2d2c4ba44c386203])) else (if j < 58 then (cbits [0xd2512db2502d6f44,0x2719c31910e3142d,0x62234b9ba3332c23,0xa94b2c89332c492c,0x502ccc4ba46c382c,0x19e6251106202d12]) else (cbits [0xe0342c7250a48c38,0x381a06251126202c,0x96008a4af442c6c,0x4314ecc0352cc01d,0x140980082d463411,0x1a26311186201163])))) else (if j < 63 then (if j < 61 then (if j < 60 then (cbits [0x9250a4cf449c063f,0x501a493d11a92c2d,0x2d032909a314a4f2,0x263f1a663111c620,0x202d9250a50f449c,0xa52f441a863111e6]) else (cbits [0x462712062009c314,0x2c62a63f9c46331c,0x6da93f2a29332549,0xf44edac3fa54c38,0x202e20132e4f452e,0x1c693312292c09e6])) else (if j < 62 then (cbits [0x6c3f256c389c693f,0x44124c38a56f442a,0x12692ca59250258f,0x89499c893f1c8933,0x492a8c3f25ac3862,0xed8f49a5af446d8c]) else (cbits [0xa6331ca627128620,0x2c62c64b22663d9c,0x2d693d2aa93325c9,0x6c3da5cc386dc94b,0x502e8f4aedcc4bad,0x12a6202ed2516e52]))) else (if j < 65 then (if j < 64 then (cbits [0xe92c9cc6331cc627,0x50a5ec382ac93325,0x260c3812c92c2eb2,0x2c3812e92ca60f44,0x82eb254a62f4426,0x2fc0372f00350a00]) else (cbits [0xe3271ce31b130314,0x2c2ae6272646209c,0x2e8f44302c38a649,0x31b1323146e9250,0x202f233f9d03271d,0x2f663f2b06272666])) else (if j < 66 then (cbits [0xaf44af693fa6692c,0x499d26321d26262f,0x1d4630af4c492f49,0x29322f43491d6325,0x202b493c2f8c492b,0xa68c3826892c1346]) else (if j < 67 then (cbits [0x83271d831b136314,0x2726a6202fe3499d,0xa6a92c3006492b66,0xa6321da626b00949,0x271386200a23149d,0x26c92c9de6331de6]) else (cbits [0xa314a6cc382ba933,0x209e03271e031b13,0xa6e92c2bc62726e6])))))))) 24 (i % 16)
def s119Forest (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0x1e0200400407e00,0x9980d8700449600c,0x400701901c036024,0x981cc4a0761c024c,0xe18a0098700731,0x49603cc4]) else (if j < 2 then (cbits [0x8700f49983d87010,0x1383987e0f7a204d,0xa018319839e88163,0xf839e881a61c03a4,0x41e18d8098701c61,0x49807cc6]) else (cbits [0x2641e7a207d87020,0x2809527c1e7a208d,0x7e1e7a209d8701e9,0x80ade881e19a0a58,0x6021a00b5e961e92,0x4960bc66]))) else (if j < 4 then (cbits [0x2662f9280c187030,0x940d52962f1940cd,0x583831000a4a02f1,0xf8e5e883a61c0e52,0x389280f52663861,0x7a20fd87]) else (if j < 5 then (cbits [0xc4e0261c10587e38,0xa211001c4431010c,0x964392811de88437,0x592cc6602320125e,0x292812cc684c62,0x7a213d87]) else (cbits [0x120161c14587e02,0x1c1552585431014c,0x4e5331415d266546,0xf1658705a18e164c,0xc5919a1758785c49,0x19a17d87])))) else (if j < 9 then (if j < 7 then (cbits [0x8706249614de8859,0x951906506449994d,0x406818a005258641,0x21ad8706a4961a4c,0x66a61f9a98726a7a,0x4999a588]) else (if j < 8 then (cbits [0x4a0707a21c0c5270,0xa29d1e887461c1a6,0x7e697a51dd872697,0x19a58707931a9e58,0x87e18e9f4c4e6862,0x7a21f925]) else (cbits [0xe8a7d928205e887d,0xa79f4c80847a59f5,0x588818ea1cc66687,0xa22d896879282212,0x87928235e888731,0x928a1e4a]))) else (if j < 10 then (cbits [0x26927a224587068,0xa5255872687a2a44,0x7e68928a564a0967,0xba65e889a19aa658,0x6016219a18709919,0x8a7c63]) else (if j < 11 then (cbits [0xe88a161c284c40a0,0x1fa80c66a0310a81,0x7ea07a229d870a03,0x82ade88a001a2a58,0x49f0202b5e96a092,0x4982bcc6]) else (cbits [0x870b14962c4052b0,0x1c2c0068b461fac5,0x7eb061cac1e88b66,0x22bd886b001aae58,0x6af7a2abe4a0bc7a,0x20afde9]))))) else (if j < 18 then (if j < 15 then (if j < 13 then (cbits [0x52c249927de9eaf,0xa5b0de88c349630c,0xa0c87a2308080c67,0xb2de96c27a2b0a4,0x2ce49f27de9ec202,0x49633c05]) else (if j < 14 then (cbits [0x4a0d27a233a4a0cf,0x1c27e4a2ce92833a,0x8ad692835de88d66,0x7b58c80da7a5b59e,0x8dd01ab7587e9f7a,0x92837c66]) else (cbits [0xe889faae3764a0dd,0xa2a7e4a2e392838d,0x82e87a5a7e4ace67,0x53a5290ea3253a40,0xe832a3b4086e84a,0x7a23a068]))) else (if j < 16 then (cbits [0x22f2199805e9e9f,0x283d1258f43103cc,0x58f3325bccc4ef39,0x9bce4a0f961c3e52,0xfe4a5bcc050fc49,0x9283cc05]) else (if j < 17 then (cbits [0xe890261c405258f2,0x1a41589701928409,0xa10192841de89013,0x4c2d266f2928c064,0x10b9284346510b01,0xaae42e4a]) else (cbits [0x65111014c45296f2,0x283ca4a1147a23c8,0x59183100064a2f29,0x2c69e891a61c4652,0xf197a5475873197a,0x31ac7d87])))) else (if j < 21 then (if j < 19 then (cbits [0x26718621c658711f,0x2849187124194c8d,0xa12392849de89239,0x24ad87118928c8e4,0x3187a2cac0272c7a,0x7a54bd87]) else (if j < 20 then (cbits [0x87f18928cbe4a130,0x9bccde893419accd,0x4e01621c61871331,0x64e864f3a00ece4c,0xd3e49fce9e893c49,0x7a24ea4a]) else (cbits [0x81427a5cea4a140,0x2551403f39021508,0x994892bd164a1456,0x852de894a3104e40,0xf4a7a5d29e8b4a92,0x321ce5e9]))) else (if j < 23 then (if j < 22 then (cbits [0x57527a24e6ab950,0xa2ce64a352928548,0x83587a5ce64ad567,0x1d618915a4a55640,0xf397a2560c815802,0x319805e9]) else (cbits [0x25961193d8403b60,0xa5d852676192858d,0xa16101a59d897614,0x2580c696a625d824,0x3609285824a16c7a,0x61c0064a])) else (if j < 24 then (cbits [0xe8b70009dc5e8970,0x285d5e957461c805,0x6b7861f8064a3749,0xfde52937a19fde40,0xf787a25e58937c31,0x1a4dfc06]) else (cbits [0x8860161c5e0c937f,0x1])))))) 22 (i % 16)
def s119Links := pageLinks s119Index s119Codes 5 13 9 6
def s119Data (i : Nat) : Nat × Nat :=
  let e := s119Forest i
  (e &&& 511, e >>> 9)
def s119Sample : Nat × Nat := (s119Blob467735, 96)
def s119Tags := dagTraceTags s119Mask 96 (dagTagBases s119StockWords s119Blob468307 s119Blob468508 96) 11 s119Data
def s119Num (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 2 then (if j < 1 then (cbits [0xffffffff,0x555555555555,0xffff0000ffff,0xffffffffffff,0x55555500555555,0xff00ff00ff00ff,0x505555505055555,0x555055505550555,0xf0f0f0f0f0f0f0f,0xfff0fff0fff0fff,0x1111555511115555,0x1515151515151515,0x3333333333333333,0x4444444444444444,0x5000500050005000,0x5050505050505050]) else (cbits [0x5555555555555555,0xaaaaaaaaaaaaaaaa,0xc0c0c0c0c0c0c0c0,0xc888c888c888c888,0xc8c88888c8c88888,0xcc00cc00cc00cc00,0xcccc0000cccc0000,0xcccc888888888888,0xcccccccccccccccc,0xe0e0a0a0e0e0a0a0,0xea00ea00ea00ea00,0xeaea0000eaea0000,0xeaeaeaeaeaeaeaea,0xeeeeaaaa00000000,0xeeeeaaaaeeeeaaaa,0xf000f000f000f000])) else (if j < 3 then (cbits [0xf000fffff000ffff,0xf0f00000f0f00000,0xf0f0a0a0a0a0a0a0,0xf0f0f0f000000000,0xf0f0f0f0f0f0f0f0,0xfa00aa00fa00aa00,0xfaaa0000faaa0000,0xfaaafaaafaaafaaa,0xfafaaaaa00000000,0xfafaaaaafafaaaaa,0xfafafafaaaaaaaaa,0xfcccf000fcccf000,0xfcfcf0f0cccc0000,0xff000000ff000000,0xff00aa00aa00aa00,0xff00ff0000000000]) else (cbits [0xff00ff00ff00ff00,0xffaaaaaaffaaaaaa,0xffaaffaaaaaaaaaa,0xffc0c0c0ffc0c0c0,0xffccff00cccc0000,0xfff0ff00f0f00000,0xffff000000000000,0xffff0000ffff0000,0xffffaaaaaaaaaaaa,0xffffc0c0c0c0c0c0,0xfffff000f000f000,0xfffff000fffff000,0xffffffff00000000,0xffffffffffff0000]))) 64 (i % 16)
def s119Entry (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0x47ea00000003fb,0xa80000113be90000,0x13891b2700044e27,0x43e90008113be801,0x113fe8000011,0xd1b4700045037c8,0xe80004d143a80114,0x4501b6800059143,0x278800001137c900,0x113491b0700044d]) else (if j < 2 then (cbits [0x4d278744d2460e06,0x860113490e8702e4,0x744d278744d24304,0xec700081137c803,0x89137c802044d,0x4d0ec802244d05c7,0xc801134304c70004,0x44d13c7000dd137,0x47c800001347e900,0x205934707000593]) else (cbits [0xd10ec78164d10e06,0xa700081347a80164,0x89347a80204d10e,0x1b680224d105a700,0x134460e670004d1,0x3447e7000b9347e8,0xe70004d10ee80000,0xdd347e801344304,0x47e900003a47e700,0x5d127a8000017]))) else (if j < 4 then (cbits [0x4905a70174491b27,0xe700081747e80174,0x91747e800002c47,0x5e800002d47e700,0x1127a90005d1,0x460e270004491b28,0x2744918304260112,0xb9127a80374491b,0xea802e44905a700,0x1124304a7000449]) else (if j < 5 then (cbits [0x4913a7000dd127a8,0xe800002047e90004,0x1123e70000112b,0xee800044a0ee700,0x2044304e7000811,0x3b47e7000de047e8,0xe800002247e90000,0x3647e7000c2247,0xee900089105e800,0x44304e8000011]) else (cbits [0x1113e800003747e9,0xd900000047fa0000,0x44d279800001137,0x37d80113491b1700,0xa1137c7000811,0x1d47e800001347f9,0xd80007511b670000,0x593471700059347,0x47b8028593470602,0xa1347a7000813])))) else (if j < 9 then (if j < 7 then (cbits [0x1127b90004d11b78,0xf90004491b380000,0x2847e800002047,0x2bf8000a2047e800,0x37da000011,0x491b1800000d2799,0x1600d2460e170003,0xd2460f1734918304,0x1b170373491b1700,0xb8d279803e349]) else (if j < 8 then (cbits [0x490e97000c8d2797,0x9802e349059702e3,0xd24304970003490e,0xf9800d243069700,0x373490e97000349,0x4d2797000dcd2798,0x980003491397000e,0x2037d9000f8d27,0x23d700002837d800,0xa0d0ed700000d]) else (cbits [0x4304d700080d0ed8,0xd800080d0fd80203,0x3b37d7000de037,0x37d9000fa037d800,0x2a37d8000022,0x8d05d700000d1fd7,0xd7000c2237d8000a,0x88d0ed800003637,0x5d802234304d700,0x88d07d800088d]))) else (if j < 10 then (cbits [0x4304d800000d0ed9,0xd800d10304d70003,0xd0fd900034306,0x4d7000dcd0ed800,0x34307d8037343,0x3937d800003737d9,0xd800000d0bd70000,0xd13d8000e7737,0x4ffa00003e37d900,0x77f9000000]) else (if j < 11 then (cbits [0xc1b7700000033f8,0xf800000c0ef70000,0x1d6ff800001d33,0x1b7800001d73f800,0x7460e7700001d,0x3277e700002e77f8,0xf700001d0ef80000,0x3777f800074304,0x4fd900003977e700,0x8164f18000016]) else (cbits [0x932316000a164f17,0x160285930e160005,0x9a164f05037a164f,0x4160205930e1703,0x205930f178164c3,0x164f160378164f17,0xd803e8164f170398,0x64c304d70005930e,0x4fd80005930fd801,0xe564fd7000dd6]))))) else (if j < 18 then (if j < 15 then (if j < 13 then (cbits [0x204fb9000f964fd8,0xb70000284fb80000,0xa130eb700001323,0x4fa6000de84fb700,0x8130eb8000e68,0x130fb80204c304b7,0xb7000de04fb80008,0xfa04fb8000e604f,0x4fb80000224fb900,0x131fb700002a]) else (if j < 14 then (cbits [0x930eb8000a9305b7,0xb80224c304b70008,0x89307b800089305,0xe780000131b7900,0x1318304770004c6,0xd31b780004c60f78,0x7800003a1b77000d,0x2e4ff9000f931b,0xd3f80000324ff800,0x3405f7000000]) else (cbits [0x9305f8000b930ef8,0xf80000130ef9000b,0x4c306f80004c304,0xef80000130ff900,0x374ff9000dd3,0x584fd70000394ff8,0xb70008d84f96000e,0xe774ff8000e634f,0xebf8000dd84fd700,0x1313f8000000]))) else (if j < 16 then (cbits [0x5ffa00003e4ff9,0xf80000007ff90000,0xb27b70000002f,0x6bf800000b05f700,0x1f7bf800001f,0xc91b3700001f27b8,0xf80007c905b70007,0x287fe70000207f,0x7fe70000247ff800,0x1f05f800002b]) else (if j < 17 then (cbits [0xc91b3800001727b9,0x370172460e370005,0xc1727b801724605,0xeb800003527b700,0x1724304b70005c9,0xc907b80005c905b8,0xf80000205ff90005,0xb3f80000285f,0xef800002c05f700,0x81705f8000817]) else (cbits [0x2b5ff80000245ff9,0xf9000000b7f80000,0x5c304f80000170e,0x7f900001705f900,0x27ba000017,0x460e380000091b39,0x3700918304370002,0x2460f3800918306,0x1b380372460e3700,0xe491b37000dc9])))) else (if j < 21 then (if j < 19 then (cbits [0x891b380002461337,0xb800002e27b9000f,0x917b700003227,0xeb8000c8905b700,0x2e24304b7000b89,0x8907b8000b8905b8,0xb80000090eb9000b,0x910304b700024304,0xfb900024306b800,0xdc90eb8000009]) else (if j < 20 then (cbits [0x4307b803724304b7,0xb800003727b90002,0x90bb700003927,0x13b8000e7727b800,0x3e27b9000009,0xa3f900000083fa,0xf800002853f80000,0x80ef700000023,0x9ef70000289ff800,0x280ef8000de8]) else (cbits [0x37a3f8000a0304f7,0xe7000039a3e70000,0x2883f9000e77a3,0xef800002783f800,0xde883f8000a20,0x2bf9000e6883e7,0xf700000a0ef80000,0xa0ff800028304,0x2bf80000372bf800,0x3c83f900003e]))) else (if j < 23 then (if j < 22 then (cbits [0x200ef9000f2005f8,0xf80008600ef80000,0x80306f800080304,0xef80000200ff900,0x3783f9000de0,0x6383b700003983f8,0xf8000be38336000e,0xeff8000e7783,0x83f900002013f800,0x8bfa00003e]) else (cbits [0x2a57f8000000abf9,0xf70000001ff80000,0x2a9bf800000705,0xabf800002aa7f800,0x33abe7000030,0x308bf900002a05f8,0xf9000000dbf80000,0x88304f80000220e,0x7f900002205f900,0xefa000022])) else (if j < 24 then (cbits [0x304f800000304f9,0xfa00000306f90001,0x370ef90000000f,0x7f9000dc304f800,0xdffa000003,0x3963f8000000e7f9,0xf800002363f70000,0x2f8ff70000398f,0xdff90000000bf800,0x3763f8000039]) else (cbits [0x13f90000378ff8,0xfbfa0000])))))) 40 (i % 16)
def s119Ids (i : Nat) := materialize [17, 24, 36, 48, 55, 60] 6 63 5 (s119Entry i >>> 4)
def s119Words (i : Nat) := (s119Ids i).map s119Num
def s119States (i : Nat) : Option (Nat × List Nat × List (Nat × Nat × Nat)) := some (s119Entry i &&& 15, s119Words i, shortHist s119Mask 11 s119Words s119Data i)
def s119MoveCert : List (((List (List (Nat × Nat) × List (Nat × Nat))) × (Fin 64 → Fin 64) × (Fin 64 → Fin 64))) := [(pm6, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 2, 3, 5, 4] 0 i.val))), (pm0, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 4, 5] 0 i.val))), (pm9, (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 5, 4] 0 i.val)), (fun i : Fin 64 => Fin.ofNat 64 (permuteAxes [0, 1, 3, 2, 5, 4] 0 i.val)))]
def s119Moves := dagMoves s119MoveCert
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Autos : DagMovesOK s119Mask s119Goal 64 s119Moves := dagMovesOfCheck (by decide +kernel)
def s119Choice (i : Nat) : Nat :=
  let j := i / 16
  unpack (if j < 12 then (if j < 6 then (if j < 3 then (if j < 1 then (cbits [0x1fc3c304001f,0x3f070608000e000,0x8e8d14401c000190,0x208800800032f87e,0x607065050,0x0,0x10000000010000,0x67e4e4c98201c080,0x4041002008004324,0x230803001c6043c0,0x20c018d1112,0x0,0x3046104040882104,0x40000024,0x1102208030444004,0x821e0e0080c11991,0xc1c0001900364644,0x320058c8c1939,0x8]) else (if j < 2 then (cbits [0x0,0x0,0x4000000,0x0,0x0,0x4000,0x100f81010830802,0x20000004,0x20008a1008000000,0x240e60,0xa2e0000000000000,0x19003e49bca29,0x4,0x5200020410808000,0x40000000000640,0x40100e0000000000,0x400019333f2726,0x300060600001860,0xc3000000042008,0x4]) else (cbits [0x8000,0x20000000,0x803004000000,0x10040000040041d0,0xa010000000000000,0x80411c40010000,0x1400,0x6704040823004000,0x20024,0x0,0x40000400000,0x80000000000001,0x1262304040812004,0x0,0x140000000000000,0x10000000000801,0x81c0000000000000,0x361d7e1c0c510,0x2432602000821008]))) else (if j < 4 then (cbits [0x0,0x0,0x20000000000,0x100,0x0,0x800000000,0x0,0x5101000410804000,0x94890f4038000321,0x596c0700006400b4,0x20000c800c989a,0x0,0x0,0x20000000000,0x4001042010000000,0x40480780,0x85c0000000000000,0x32007a55b4c6a,0x8]) else (if j < 5 then (cbits [0xc82280004082101,0x8000000000,0x2e2412101c000000,0x10421080023221fe,0x1c004300404,0x8,0x10000,0xe02020021004000,0x40000000122,0x80000000000000,0x200004,0x0,0x36077e1a0c51081c,0x1000000000000000,0x0,0x2084020000000000,0x85c0001902900800,0x32007e11fc510,0x2800e3c3d8e318f8]) else (cbits [0x2f82bf83870c2107,0x5400808104212000,0xf0c1003fc000090,0x2087bf800032007f,0x3f00006400fb1b1,0xc000c4040000,0x0,0x20080000,0x40000002020,0x2008ff0000000000,0x18e0000c998c5050,0x11820188081000,0x0,0x80330000,0x80000000000,0x100000008000000,0x0,0x20000000000802,0x1000000])))) else (if j < 9 then (if j < 7 then (cbits [0x90000000000042,0x3da5a243d17e000,0x10000027c000190,0x427f8000300061,0x6700046443c2424,0x8ca0184040009,0x10000,0x20080001,0x1b120878f8802000,0x64e71f00000000fb,0x63e00000001e7270,0x38f0f638c,0x4,0x0,0x0,0x0,0x8,0x10000,0x3e02002821088]) else (if j < 8 then (cbits [0x0,0x0,0x0,0x3a52878000000000,0x100002800f3ac6,0x0,0x0,0x301ff0410844000,0x140,0x821190000000000,0x2c0004,0x808000,0x10000000,0x6213e0000008000,0xb68418f3f00003e0,0x83000e00280007f6,0xc000388080,0x20,0x40000]) else (cbits [0x40003c0808418421,0x10000002,0x20020000000000,0x40000001000100,0x100002,0x0,0x80000008010000,0x77d9989453c7c001,0x40a0098001140,0x5200062,0x0,0x0,0x800000000000,0x0,0x4101142110000000,0x400cc0,0x8440000000000000,0x8005301000450,0x4002000000000,0x1]))) else (if j < 10 then (cbits [0x5001f649e514d0f,0x393134b2d80e000,0x100000000001e0,0x410848000000000,0xf1f000242003fe02,0x5001f67fe514,0x801480808104232,0x10000000000,0x2020000000000000,0x492f1f00010a0000,0x320006700bf6366,0x31800080889040,0x10000000,0x20200000c0000,0x4040820190000000,0x821e3e0002000a40,0x17c0000f803ec6fc,0x667f4f4c802,0x6400fe1e1c0040f8,0x7]) else (if j < 11 then (cbits [0xe0100c4040810807,0x0,0x0,0x0,0x60000008000000,0x800,0x80000006,0x71010000001c000,0x1800,0x0,0x800c000400000,0x800000000,0x940031000200001c,0x2,0x40000000000000,0x10006000000,0x1f80000001000008,0x3000606d0d09860,0xc30202000423c0,0x4]) else (cbits [0x6418000000208000,0x10000000,0x20000000000,0x0,0x2,0x4000,0x8030400000010802,0x20000001,0x40000000000,0x80000002000200,0x200004,0x8000,0x1200000010020000,0xc000038e0038002,0x10000006000c,0x2280000000000000,0x180000000000,0x2800010040,0x20000000]))))) else (if j < 18 then (if j < 15 then (if j < 13 then (cbits [0x8000001c010000,0xed85824018fa000,0x80401c003002,0x1000000001904050,0x0,0x200,0x8000000,0x10000000000,0x1006008000000,0x200800000a0081a0,0x0,0x8000800000401,0x800010802000,0x20000000000,0x42008000000000,0x14ba0008480000,0x480108a23ad85a2,0x229040100040004]) else (if j < 14 then (cbits [0x0,0x3880020009402000,0x2800010082,0x5008000000000,0xa000041008a20008,0x2000800000000,0x233bb3b0f118be,0x270404083310c010,0x21004,0x40000000000000,0x84001000010,0x1002028000,0x2000,0xa0000000000,0x410304a520000028,0xc4011fc1,0x80900a0060000000,0x118a00700020c42,0x4002,0x20]) else (cbits [0x400000000000,0x800000000000804,0x50fcc1293c008000,0x103421800114627f,0x300c060808,0x2000801000002,0x8a33182ff86094a4,0x2004000000000000,0x80a1414afc001000,0x2800300cd60,0x10010030001414,0x0,0x0,0x0,0x40000000000000,0x0,0x4080000000000008,0x38200701050042,0x800080a0010004,0x1]))) else (if j < 16 then (cbits [0x7d98c53fc200842,0xebf8e8628843e000,0xc0e18087c0008a0,0x4101088406b6007f,0xca02022030,0x0,0x0,0x80000000,0x48000000,0x8002110000000002,0xa4000c4000,0x0,0x0,0x40000000,0x8000080c000,0x400,0x2004001000000,0x2000000000,0x7000200004101088,0xc]) else (if j < 17 then (cbits [0x45065ed65131ea1f,0xc380800208422000,0x0,0x0,0x0,0x200000000,0x0,0x9301080410844000,0x100,0x1042110000000000,0x20044c0400,0x2004000800000,0x19f030204318c0,0x40000008,0x2020c6000802012,0x10012801c0,0x0,0x4000001000000020,0x2000000040000]) else (cbits [0x6ec0404186318,0x8000000000000020,0x4080018c00200800,0x8a210f8482020070,0x2110100283afe21f,0x1401440420104,0xde0ab87e8e38c62e,0xd1ff010618c60000,0x96890f40f80816c1,0x596c1f00000000f6,0xc1e00000001cd8da,0xa0039be4c925,0x4,0x0,0x7fc1042110000000,0x500180,0x4640000000000000,0x8600010208,0x2020000000])))) else (if j < 21 then (if j < 19 then (cbits [0x4000000,0x3081f8000002000,0x5344c7a87c0000f8,0x8080a80111401fb,0x212100c2000,0x0,0x0,0x1e01020410844000,0x10100,0x1042110000000000,0x42000580400,0x4000400800000,0x14007b54b4c6a83c,0xe94949cc5838000,0x40000000000780,0x1042120000000000,0x87c000908017f808,0x14007b5ff4c7a,0x20114020204108c8]) else (if j < 20 then (cbits [0x4000000,0x808000000000,0x4b54a7a47c000428,0x40080c80019c08fb,0x4610040222,0x4000,0x808000030,0x8a01010200464000,0x97e90f40f8000800,0x4843f00003e00f6,0x3e00080087fcbc9,0x400d9403f8782092,0x24004,0xc20201048038000,0x80000007010,0x1000c0000000000,0x80,0x20,0x2900c20000048038,0x1]) else (cbits [0x8000,0x8010000000,0x1010020000400c80,0x80,0x270000000000002,0x2038c001c4040009,0x80080000001000c,0x20080000,0x40000000000,0x80000000000000,0x87e0000000000000,0x70010ff9792490,0x421802000821084,0x4000000e,0x80080000000000,0x100000000100400,0x14000000008,0x800000000030020,0x2e00e007e1060100,0x101c]))) else (if j < 23 then (if j < 22 then (cbits [0x8008000,0x7f987a298c5e000,0x200200000018a1,0x42108000000000,0x30040c0404,0x2000200800008,0x8a10f01ff8218c60,0x800000020000401,0x40604529cc000000,0x800090000053c0,0x2018400000404,0x8000,0x10000000,0x20000000000,0x40c20a0000000000,0x1000121000801c0,0x800014000000008,0x21f21e12ff0021,0x280efe3618a210f8,0x2]) else (cbits [0xada01fc28384501f,0x2000400,0x14201404c000000,0x2908421,0x20000000000000,0x800,0x8000000014,0x800000000000000,0x1000800,0x8050130000000100,0x6300008e20080000,0x58000370080830c,0x200702040618000,0xefe21f8a210f90c0,0x4101042110100280,0x38c62e0002401480,0xc60000de02b87d8e,0x81ac072ff010618,0x2800fe21f8a21078])) else (if j < 24 then (cbits [0xf001c383b1c6307,0x8104212000,0xf0fc718c3e0000e0,0x8a210f80013d007f,0x31f00002800fe3ff,0x2702bfc43f1c6,0x805400808104232,0xffff0618c60000,0x1e386108f80809d0,0x86101f00033815fe,0x10018fa01f87c7,0x808002,0x0,0x2020100000000,0x40000000000000,0x420320000000000,0x600034940008889,0xb000701112084,0x20002000000c]) else (cbits [0x80004000002,0x57f8f8e18423e000,0xffc10007c000c80,0x1f007f])))))) 77 (i % 16)
def s119Check := dagCheckNode s119Mask s119Goal s119Chart (fun i => dagKnownCloses s119Goal (cutPick s119Cuts (s119Choice i))) 387 s119States s119Moves s119Links s119Sample s119Tags
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Roots : dagCheckRoots s119Mask s119Goal s119Chart (dagKnownCloses s119Goal s119Cuts) s119Witnesses (dagRef 387 s119States s119Moves s119Links 0) s119StockWords 11 = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block0 : treeBlock 0 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block24 : treeBlock 24 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block48 : treeBlock 48 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block72 : treeBlock 72 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block96 : treeBlock 96 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block120 : treeBlock 120 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block144 : treeBlock 144 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block168 : treeBlock 168 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block192 : treeBlock 192 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block216 : treeBlock 216 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block240 : treeBlock 240 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block264 : treeBlock 264 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block288 : treeBlock 288 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block312 : treeBlock 312 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block336 : treeBlock 336 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block360 : treeBlock 360 24 s119Check = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Block384 : treeBlock 384 3 s119Check = true := by decide +kernel
theorem s119Group0_48 : treeBlock 0 48 s119Check = true := treeBlock_merge (start := 0) (left := 24) (right := 24) (check := s119Check) s119Block0 s119Block24
theorem s119Group48_48 : treeBlock 48 48 s119Check = true := treeBlock_merge (start := 48) (left := 24) (right := 24) (check := s119Check) s119Block48 s119Block72
theorem s119Group0_96 : treeBlock 0 96 s119Check = true := treeBlock_merge (start := 0) (left := 48) (right := 48) (check := s119Check) s119Group0_48 s119Group48_48
theorem s119Group96_48 : treeBlock 96 48 s119Check = true := treeBlock_merge (start := 96) (left := 24) (right := 24) (check := s119Check) s119Block96 s119Block120
theorem s119Group144_48 : treeBlock 144 48 s119Check = true := treeBlock_merge (start := 144) (left := 24) (right := 24) (check := s119Check) s119Block144 s119Block168
theorem s119Group96_96 : treeBlock 96 96 s119Check = true := treeBlock_merge (start := 96) (left := 48) (right := 48) (check := s119Check) s119Group96_48 s119Group144_48
theorem s119Group0_192 : treeBlock 0 192 s119Check = true := treeBlock_merge (start := 0) (left := 96) (right := 96) (check := s119Check) s119Group0_96 s119Group96_96
theorem s119Group192_48 : treeBlock 192 48 s119Check = true := treeBlock_merge (start := 192) (left := 24) (right := 24) (check := s119Check) s119Block192 s119Block216
theorem s119Group240_48 : treeBlock 240 48 s119Check = true := treeBlock_merge (start := 240) (left := 24) (right := 24) (check := s119Check) s119Block240 s119Block264
theorem s119Group192_96 : treeBlock 192 96 s119Check = true := treeBlock_merge (start := 192) (left := 48) (right := 48) (check := s119Check) s119Group192_48 s119Group240_48
theorem s119Group288_48 : treeBlock 288 48 s119Check = true := treeBlock_merge (start := 288) (left := 24) (right := 24) (check := s119Check) s119Block288 s119Block312
theorem s119Group360_27 : treeBlock 360 27 s119Check = true := treeBlock_merge (start := 360) (left := 24) (right := 3) (check := s119Check) s119Block360 s119Block384
theorem s119Group336_51 : treeBlock 336 51 s119Check = true := treeBlock_merge (start := 336) (left := 24) (right := 27) (check := s119Check) s119Block336 s119Group360_27
theorem s119Group288_99 : treeBlock 288 99 s119Check = true := treeBlock_merge (start := 288) (left := 48) (right := 51) (check := s119Check) s119Group288_48 s119Group336_51
theorem s119Group192_195 : treeBlock 192 195 s119Check = true := treeBlock_merge (start := 192) (left := 96) (right := 99) (check := s119Check) s119Group192_96 s119Group288_99
theorem s119Group0_387 : treeBlock 0 387 s119Check = true := treeBlock_merge (start := 0) (left := 192) (right := 195) (check := s119Check) s119Group0_192 s119Group192_195
theorem s119Blocks : treeBlock 0 387 s119Check = true := s119Group0_387
theorem s119Known : Known s119Cuts := (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (extendKnown (show Known [] from fun _ h => False.elim (List.not_mem_nil h)) s70Stock) s83Stock) s28Stock) s27Stock) s9Stock) s21Stock) s8Stock) s36Stock) s43Stock) s118Stock) s24Stock) s2Stock) s117Stock) s40Stock) s68Stock) s37Stock) s1Stock) s20Stock) s16Stock) s67Stock) s66Stock) s17Stock) s116Stock) s115Stock) s114Stock) s113Stock) s110Stock) s111Stock) s109Stock) s108Stock) s107Stock) s106Stock) s105Stock) s31Stock) s12Stock) s104Stock) s103Stock) s102Stock) s101Stock) s100Stock) s99Stock) s98Stock) s71Stock) s97Stock) s96Stock) s95Stock) s94Stock) s93Stock) s87Stock) s86Stock) s72Stock) s64Stock) s63Stock) s62Stock) s61Stock) s60Stock) s59Stock) s58Stock) s57Stock) s56Stock) s55Stock) s54Stock) s53Stock) s52Stock) s51Stock) s50Stock) s49Stock) s48Stock) s47Stock) s46Stock) s42Stock) s41Stock) s39Stock) s38Stock) s35Stock) s34Stock) s23Stock)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem s119Stock : Lower s119Mask s119StockWords s119Goal 12 := by
  apply lowerDag s119Choice _ _ _ _ s119Autos _ _ _ s119Known _ s119Roots s119Blocks
  · unfold Masked; decide +kernel
  · unfold Masked; decide +kernel
  · unfold properWord; decide +kernel
  · exact chartOfCheck (by decide +kernel)
  · exact stockMaskedOfCheck (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · simp only [s119Cuts, List.mem_cons, List.not_mem_nil, or_false]
    intro b h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
end PEqualNP.Outside.L_meta_41968

open PEqualNP.Outside.L_meta_41968 in
theorem PEqualNP.Outside.L_meta_41968 : (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808362 * 2 ^ 32 + 3937060992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808362 * 2 ^ 32 + 3937060992) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) := by
  intro t h
  let raw : List (BitVec 64) := [0xaaaaaaaaaaaaaaaa,0xcccccccccccccccc,0xf0f0f0f0f0f0f0f0,0xff00ff00ff00ff00,0xffff0000ffff0000,0xffffffff00000000]
  let goal : BitVec 64 := 0xfeeaeaaaeaaac880
  have root : Lower (fullMask 64) (raw.map BitVec.toNat) goal.toNat 12 :=
    hcsLowerEq (by decide +kernel) (by decide +kernel) (by decide +kernel) s119Stock
  have size : 12 ≤ t :=
    hcsLower (n := 6) raw goal 12 _ (by decide +kernel) (by decide +kernel) root t h
  let circuit : PEqualNP.CircuitLowerBounds.Circuit :=
    ⟨[⟨.or, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.or, [2, 3]⟩, ⟨.and, [1, 10]⟩, ⟨.and, [4, 5]⟩, ⟨.or, [9, 12]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [8, 14]⟩, ⟨.or, [11, 15]⟩, ⟨.and, [16, 13]⟩], 17⟩
  refine ⟨circuit, ?_, ?_, by decide +kernel⟩
  · intro gate member
    simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact Nat.le_trans (by decide +kernel : circuit.size ≤ 12) size

