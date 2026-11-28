import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37645

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 256

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 128 := ((x >>> 128) ^^^ x).setWidth 128
def cuts (ws : List W) : BitVec 128 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 128) ++ (0 : BitVec 128)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 128) (w : W) : Prop :=
  w.getLsbD (128+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 128) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 128+i.val < 256 := by omega
  have hi' : i.val < 256 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 128) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 128)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x.toNat ≤ y.toNat then x :: y :: ys else y :: insertW x ys

def canon : List W → List W
  | [] => []
  | x :: xs => insertW x (canon xs)

theorem insertW_perm (x : W) : ∀ l : List W, (insertW x l).Perm (x :: l)
  | [] => List.Perm.refl _
  | y :: ys => by
    unfold insertW
    split
    · exact List.Perm.refl _
    · exact ((insertW_perm x ys).cons y).trans (List.Perm.swap _ _ _)

theorem canon_perm : ∀ l : List W, (canon l).Perm l
  | [] => List.Perm.refl _
  | x :: xs => (insertW_perm x (canon xs)).trans ((canon_perm xs).cons x)

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (fun e l => optimized k e (canon l)) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (fun e l => optimized k e (canon l)) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        have hcn : (canon (z :: kept)).Perm (z :: kept) := canon_perm _
        apply dispatch_complete (k := k) (extra := extra) (fun e l => optimized k e (canon l)) hop hk (by omega) (by omega) (cuts_full hg hl)
        refine ih _ _ (hcn.nodup_iff.mpr hnd) ?_ (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl)
        rw [hcn.length_eq]; simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) (canon ws)

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  have hcn : (canon ws).Perm ws := canon_perm ws
  have hopt : optimized n (n+1-ws.length) (canon ws) = true :=
    optimized_complete hg n (canon ws) _ (hcn.nodup_iff.mpr hnd) (by rw [hcn.length_eq]; omega) (by rw [List.toFinset_eq_of_perm _ _ hcn]; exact hl')
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', hopt]⟩

def kidsOf (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, canon (w :: r))] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, canon (w :: a :: r))] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, canon (w :: b :: r))] else []) ++
  (if extra ≥ 2 && (v ||| sep a ||| sep b == -1) then [(extra - 2, canon (w :: a :: b :: r))] else [])

def children (c : ℕ × List W) : List (ℕ × List W) :=
  (pairs c.2).flatMap fun p => (ops p.1 p.2.1).flatMap fun w => kidsOf c.1 p.1 p.2.1 p.2.2 w

def goalFree (ws : List W) : Bool := !(ws == [goal] || ws == [~~~goal])

theorem dispatch_false {extra k : ℕ} {a b : W} {r : List W}
    (h : ∀ w ∈ ops a b, ∀ c ∈ kidsOf extra a b r w, optimized k c.1 c.2 = false) :
    dispatch extra (fun e l => optimized k e (canon l)) a b r = false := by
  unfold dispatch
  rw [List.any_eq_false]
  intro w hw hcon
  have h1 := h w hw
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne] at hcon
  rcases hcon with (⟨hv, hn⟩ | ⟨hx, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx, hv⟩, hn⟩
  · have := h1 (extra, canon (w :: r)) (by simp [kidsOf, hv])
    simp_all
  · have := h1 (extra - 1, canon (w :: a :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 1, canon (w :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all
  · have := h1 (extra - 2, canon (w :: a :: b :: r)) (by simp [kidsOf, hv, hx])
    simp_all

theorem opt_false {k e : ℕ} {ws : List W} (hg : goalFree ws = true)
    (h : ∀ c ∈ children (e, ws), optimized k c.1 c.2 = false) :
    optimized (k + 1) e ws = false := by
  unfold optimized
  rw [Bool.or_eq_false_iff]
  refine ⟨by simpa [goalFree] using hg, ?_⟩
  rw [List.any_eq_false]
  rintro ⟨a, b, r⟩ hx hcon
  have key := dispatch_false (extra := e) (k := k) (a := a) (b := b) (r := r)
    (fun w hw c hc => h c (List.mem_flatMap.mpr ⟨(a, b, r), hx, List.mem_flatMap.mpr ⟨w, hw, hc⟩⟩))
  simp_all

def FalseAt (k : ℕ) (L : List (ℕ × List W)) : Prop := ∀ c ∈ L, optimized k c.1 c.2 = false

theorem falseAt_expand {k : ℕ} {L : List (ℕ × List W)}
    (hg : ∀ c ∈ L, goalFree c.2 = true) (h : FalseAt k (L.flatMap children)) : FalseAt (k + 1) L := by
  intro c hc
  exact opt_false (hg c hc) (fun c' hc' => h c' (List.mem_flatMap.mpr ⟨c, hc, hc'⟩))

def expandN : ℕ → List (ℕ × List W) → List (ℕ × List W)
  | 0, L => L
  | d + 1, L => expandN d (L.flatMap children)

def allGoalFree : ℕ → List (ℕ × List W) → Bool
  | 0, _ => true
  | d + 1, L => L.all (fun c => goalFree c.2) && allGoalFree d (L.flatMap children)

theorem falseAt_expandN : ∀ (d : ℕ) {j : ℕ} {L : List (ℕ × List W)},
    allGoalFree d L = true → FalseAt j (expandN d L) → FalseAt (j + d) L
  | 0, _, _, _, h => h
  | d + 1, j, L, hg, h => by
    simp only [allGoalFree, Bool.and_eq_true, List.all_eq_true] at hg
    exact falseAt_expand hg.1 (falseAt_expandN d hg.2 h)

def level0 (n : ℕ) (inputs : List W) : List (ℕ × List W) :=
  (inputs.sublists.filter (fun ws => decide (ws.length ≤ n + 1) && (cuts ws == -1))).map
    (fun ws => (n + 1 - ws.length, canon ws))

theorem search_of_false {n : ℕ} {inputs : List W} (h : FalseAt n (level0 n inputs)) :
    search n inputs = false := by
  unfold search
  rw [List.any_eq_false]
  intro ws hws hcon
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcon
  obtain ⟨⟨hl, hc⟩, ho⟩ := hcon
  have hmem : (n + 1 - ws.length, canon ws) ∈ level0 n inputs := by
    simp only [level0, List.mem_map, List.mem_filter]
    exact ⟨ws, ⟨hws, by simp [hl, hc]⟩, rfl⟩
  have := h _ hmem
  simp_all

theorem search_false_of_chunks {n d j : ℕ} {inputs : List W} (hj : j + d = n)
    (hg : allGoalFree d (level0 n inputs) = true)
    (hl : FalseAt j (expandN d (level0 n inputs))) : search n inputs = false := by
  subst hj
  exact search_of_false (falseAt_expandN d hg hl)

def chunkOK (j : ℕ) (L : List (ℕ × List W)) : Bool := L.all fun c => !optimized j c.1 c.2

theorem falseAt_of_chunkOK {j : ℕ} {L : List (ℕ × List W)} (h : chunkOK j L = true) : FalseAt j L := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simpa using this

def hashW (acc : ℕ) (w : W) : ℕ := (acc * 31 + w.toNat) % 1000003

def hashS (nb : ℕ) (c : ℕ × List W) : ℕ := (c.2.foldl hashW c.1) % nb

def inB (bk : List (List (ℕ × List W))) (c : ℕ × List W) : Bool :=
  (bk.getD (hashS bk.length c) []).any fun x => decide (x = c)

theorem inB_mem {bk : List (List (ℕ × List W))} {c : ℕ × List W} (h : inB bk c = true) :
    c ∈ bk.flatten := by
  unfold inB at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  rw [List.mem_flatten]
  by_cases hi : hashS bk.length x < bk.length
  · exact ⟨bk.getD (hashS bk.length x) [], by simp [List.getD_eq_getElem?_getD, hi], hx⟩
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)] at hx

def windowsF (j : ℕ) (L : List (List (ℕ × List W))) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => chunkOK j ((L.drop a).take s).flatten && windowsF j L (a + s) rest

theorem falseAt_of_windowsF {j : ℕ} {L : List (List (ℕ × List W))} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsF j L a sizes = true → FalseAt j (L.drop a).flatten
  | [], a, h => by
    intro c hc
    simp only [windowsF, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsF, Bool.and_eq_true] at h
    have h1 := falseAt_of_chunkOK h.1
    have h2 := falseAt_of_windowsF rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split, List.flatten_append] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsF_cons {j : ℕ} {L : List (List (ℕ × List W))} {a s : ℕ} {rest : List ℕ}
    (h1 : chunkOK j ((L.drop a).take s).flatten = true)
    (h2 : windowsF j L (a + s) rest = true) : windowsF j L a (s :: rest) = true := by
  simp [windowsF, h1, h2]

theorem windowsF_nil {j : ℕ} {L : List (List (ℕ × List W))} {a : ℕ} (h : (L.drop a).isEmpty = true) :
    windowsF j L a [] = true := h

theorem dispatch_mono {extra : ℕ} {n1 n2 : ℕ → List W → Bool} (a b : W) (r : List W)
    (h : ∀ e l, n2 e l = true → n1 e l = true) :
    dispatch extra n2 a b r = true → dispatch extra n1 a b r = true := by
  unfold dispatch
  simp only [List.any_eq_true]
  rintro ⟨w, hw, hx⟩
  refine ⟨w, hw, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true] at hx ⊢
  rcases hx with (⟨hv, hn⟩ | ⟨hx1, (⟨hv, hn⟩ | ⟨hv, hn⟩)⟩) | ⟨⟨hx1, hv⟩, hn⟩
  · exact Or.inl (Or.inl ⟨hv, h _ _ hn⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inl ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inl (Or.inr ⟨hx1, Or.inr ⟨hv, h _ _ hn⟩⟩)
  · exact Or.inr ⟨⟨hx1, hv⟩, h _ _ hn⟩

def optB (S : ℕ × List W → Bool) : ℕ → ℕ → List W → Bool
  | 0, e, ws => S (e, ws)
  | k + 1, e, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch e (fun e' l => optB S k e' (canon l)) a b r)

theorem optB_sound (S : ℕ × List W → Bool) (J : ℕ)
    (hS : ∀ c, S c = false → optimized J c.1 c.2 = false) :
    ∀ (k e : ℕ) (ws : List W), optB S k e ws = false → optimized (J + k) e ws = false
  | 0, e, ws, h => hS (e, ws) h
  | k + 1, e, ws, h => by
    have ih := optB_sound S J hS k
    unfold optB at h
    rw [Bool.or_eq_false_iff] at h
    show optimized ((J + k) + 1) e ws = false
    unfold optimized
    rw [Bool.or_eq_false_iff]
    refine ⟨h.1, ?_⟩
    have h2 := h.2
    rw [List.any_eq_false] at h2 ⊢
    rintro ⟨a, b, r⟩ hp hcon
    apply h2 (a, b, r) hp
    refine dispatch_mono a b r ?_ hcon
    intro e' l hl
    by_contra hne
    have hf : optB S k e' (canon l) = false := by simpa using hne
    have := ih e' (canon l) hf
    simp_all

def chunkB (S : ℕ × List W → Bool) (d : ℕ) (L : List (ℕ × List W)) : Bool :=
  L.all fun c => !optB S d c.1 c.2

def windowsG (f : List (ℕ × List W) → Bool) (L : List (ℕ × List W)) (a : ℕ) : List ℕ → Bool
  | [] => (L.drop a).isEmpty
  | s :: rest => f ((L.drop a).take s) && windowsG f L (a + s) rest

theorem windowsG_sound {f : List (ℕ × List W) → Bool} {P : ℕ × List W → Prop}
    (hf : ∀ X, f X = true → ∀ c ∈ X, P c) {L : List (ℕ × List W)} :
    ∀ (sizes : List ℕ) (a : ℕ), windowsG f L a sizes = true → ∀ c ∈ L.drop a, P c
  | [], a, h => by
    intro c hc
    simp only [windowsG, List.isEmpty_iff] at h
    rw [h] at hc
    simp at hc
  | s :: rest, a, h => by
    simp only [windowsG, Bool.and_eq_true] at h
    have h1 := hf _ h.1
    have h2 := windowsG_sound hf rest (a + s) h.2
    intro c hc
    have split : L.drop a = (L.drop a).take s ++ L.drop (a + s) := by
      rw [← List.drop_drop, List.take_append_drop]
    rw [split] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h1 c hc
    · exact h2 c hc

theorem windowsG_cons {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a s : ℕ} {rest : List ℕ}
    (h1 : f ((L.drop a).take s) = true) (h2 : windowsG f L (a + s) rest = true) :
    windowsG f L a (s :: rest) = true := by
  simp [windowsG, h1, h2]

theorem windowsG_nil {f : List (ℕ × List W) → Bool} {L : List (ℕ × List W)} {a : ℕ}
    (h : (L.drop a).isEmpty = true) : windowsG f L a [] = true := h

theorem search_false_B {n dp J d : ℕ} {inputs : List W} {bk : List (List (ℕ × List W))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB bk c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB bk c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB bk c = true := by simpa using hc
    exact hBF c (inB_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB bk c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB bk c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem getD_mem_or_nil {α : Type} (l : List (List α)) (i : ℕ) :
    l.getD i [] ∈ l ∨ l.getD i [] = [] := by
  by_cases hi : i < l.length
  · left
    simp [List.getD_eq_getElem?_getD, hi]
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (not_lt.mp hi)]

def inB2 (g nb : ℕ) (bk2 : List (List (List (ℕ × List W)))) (c : ℕ × List W) : Bool :=
  ((bk2.getD (hashS nb c / g) []).getD (hashS nb c % g) []).any fun x => decide (x = c)

theorem inB2_mem {g nb : ℕ} {bk2 : List (List (List (ℕ × List W)))} {c : ℕ × List W}
    (h : inB2 g nb bk2 c = true) : c ∈ bk2.flatten.flatten := by
  unfold inB2 at h
  rw [List.any_eq_true] at h
  obtain ⟨x, hx, hxc⟩ := h
  have hxc' : x = c := of_decide_eq_true hxc
  subst hxc'
  have hG := getD_mem_or_nil bk2 (hashS nb x / g)
  have hB := getD_mem_or_nil (bk2.getD (hashS nb x / g) []) (hashS nb x % g)
  rw [List.mem_flatten]
  rcases hB with hB | hB
  · rcases hG with hG | hG
    · exact ⟨_, List.mem_flatten.mpr ⟨_, hG, hB⟩, hx⟩
    · rw [hG] at hB
      simp at hB
  · rw [hB] at hx
    simp at hx

theorem search_false_B2 {n dp J d g nb : ℕ} {inputs : List W} {bk2 : List (List (List (ℕ × List W)))} {sa sb : List ℕ}
    (hj : J + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hB : windowsF J bk2.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g nb bk2 c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hBF : FalseAt J bk2.flatten.flatten := by
    have := falseAt_of_windowsF sb 0 hB
    simpa using this
  have hS : ∀ c, (fun c => !inB2 g nb bk2 c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g nb bk2 c = true := by simpa using hc
    exact hBF c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g nb bk2 c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ J hS d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + d) (d := dp) hj hg hF

theorem search_false_C2 {n dp J d g1 nb1 g2 nb2 : ℕ} {inputs : List W}
    {bkA bkB : List (List (List (ℕ × List W)))} {sa sb sc : List ℕ}
    (hj : J + 1 + d + dp = n)
    (hg : allGoalFree dp (level0 n inputs) = true)
    (hC : windowsF J bkB.flatten 0 sc = true)
    (hB : windowsG (chunkB (fun c => !inB2 g2 nb2 bkB c) 1) bkA.flatten.flatten 0 sb = true)
    (hA : windowsG (chunkB (fun c => !inB2 g1 nb1 bkA c) d) (expandN dp (level0 n inputs)) 0 sa = true) :
    search n inputs = false := by
  have hCF : FalseAt J bkB.flatten.flatten := by
    have := falseAt_of_windowsF sc 0 hC
    simpa using this
  have hS2 : ∀ c, (fun c => !inB2 g2 nb2 bkB c) c = false → optimized J c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g2 nb2 bkB c = true := by simpa using hc
    exact hCF c (inB2_mem hin)
  have hP2 : ∀ c ∈ bkA.flatten.flatten, optimized (J + 1) c.1 c.2 = false := by
    have h1 : ∀ c ∈ (bkA.flatten.flatten).drop 0, optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false := by
      refine windowsG_sound (P := fun c => optB (fun c => !inB2 g2 nb2 bkB c) 1 c.1 c.2 = false) ?_ sb 0 hB
      intro X hX c hc
      have := List.all_eq_true.mp hX c hc
      simpa using this
    intro c hc
    exact optB_sound _ J hS2 1 c.1 c.2 (h1 c (by simpa using hc))
  have hS1 : ∀ c, (fun c => !inB2 g1 nb1 bkA c) c = false → optimized (J + 1) c.1 c.2 = false := by
    intro c hc
    have hin : inB2 g1 nb1 bkA c = true := by simpa using hc
    exact hP2 c (inB2_mem hin)
  have hP : ∀ c ∈ (expandN dp (level0 n inputs)).drop 0, optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false := by
    refine windowsG_sound (P := fun c => optB (fun c => !inB2 g1 nb1 bkA c) d c.1 c.2 = false) ?_ sa 0 hA
    intro X hX c hc
    have := List.all_eq_true.mp hX c hc
    simpa using this
  have hF : FalseAt (J + 1 + d) (expandN dp (level0 n inputs)) := by
    intro c hc
    exact optB_sound _ (J + 1) hS1 d c.1 c.2 (hP c (by simpa using hc))
  exact search_false_of_chunks (j := J + 1 + d) (d := dp) hj hg hF

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
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

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 256) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

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

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 256) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#256)[k.val] = false; simp
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

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
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

set_option maxRecDepth 4000 in
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

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (4276813032 * 2 ^ 32 + 4276808864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

theorem bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 256,
      target (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target x) :
    8 < binaryCost gs := by
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
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t b inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def rows : List W :=
  [(0x8041881604147144#64 ++ 0x02010620581051c5#64 ++ 0x40cf883e0c7cf3fd#64 ++ 0xbd033e20f831f3cf#64 : BitVec 256),
   (0x011402ca11b11708#64 ++ 0x0404500b2846c45c#64 ++ 0xc3340fce33b33f3b#64 ++ 0xfb0cd03f38ceccfc#64 : BitVec 256),
   (0x04283160c2c38290#64 ++ 0xa810a0c5830b0e0a#64 ++ 0xfc38f1f1c3c3c3f7#64 ++ 0xf7f0e3c7c70f0f0f#64 : BitVec 256),
   (0x0ac0dc016c02e821#64 ++ 0x302b037005b00ba0#64 ++ 0xffc0fe01fc03fc2f#64 ++ 0x6fff03f807f00ff0#64 : BitVec 256),
   (0x0fbe0001bb680001#64 ++ 0xc03ef80006eda000#64 ++ 0xefff0001fffc001f#64 ++ 0x1fbffc0007fff000#64 : BitVec 256),
   (0x1fffefbc0000003e#64 ++ 0x007fffbef0000000#64 ++ 0xdffffffe00000000#64 ++ 0xff7ffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [9, 3]⟩, ⟨.or, [0, 10]⟩, ⟨.and, [11, 7]⟩, ⟨.or, [9, 3]⟩, ⟨.and, [1, 13]⟩, ⟨.or, [14, 12]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000004211b11700 0x040000010846c45c 0x0000000033b33f3b 0x0000000000ceccfc

def z1 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3340fce33b33f3b 0xfb0cd03f38ceccfc

def z2 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc38f1f1c3c3c3f7 0xf7f0e3c7c70f0f0f

def z3 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc0fe01fc03fc2f 0x6fff03f807f00ff0

def z4 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff0001fffc001f 0x1fbffc0007fff000

def z5 : W := mkw 0x1eebed3400000036 0x007bafb4d0000000 0x1ccbf03000000000 0x04732fc0c0000000

def z6 : W := mkw 0x8041881604147144 0x02010620581051c5 0x40cf883e0c7cf3fd 0xbd033e20f831f3cf

def z7 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe00000000 0xff7ffffff8000000

def z8 : W := mkw 0x0428212082400010 0x8010a08482090000 0xfc38f1f1c3c00017 0xf7f0e3c7c70f0000

def z9 : W := mkw 0x8000000204147140 0x02000000081051c5 0x000000000000f3e0 0x00000000000003cf

def z10 : W := mkw 0x053c23ea93f11798 0x8c14f08faa4fc45e 0x003c01fe03f003d0 0x9000f007f80fc00f

def z11 : W := mkw 0x153f33fcc2c3829e 0xa854fccff30b0e0a 0xfc3ff1ffc3c3c3f7 0xf7f0ffc7ff0f0f0f

def z12 : W := mkw 0x0b9456c979a38e29 0x342e515b25e68e38 0xbf3077c1f3830c02 0x42fcc1df07ce0c30

def z13 : W := mkw 0x0114000011200000 0x0004500000448000 0xc334000033b0001b 0x1b0cd00000cec000

def z14 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0x1000fffe00000000 0xe04003fff8000000

def z15 : W := mkw 0x9fffeffe15b5777e 0x067fffbff856d5dd 0xdffffffe3fffffff 0xff7ffffff8ffffff

def z16 : W := mkw 0x0000000000000000 0x0000000000000000 0x40cf00000c7c001d 0x1d033c000031f000

def z17 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xbc30f1f1c383c3e2 0xe2f0c3c7c70e0f0f

def z18 : W := mkw 0x1ffffffed3f397be 0xac7ffffffb4fce5e 0xfffffffff3f3ffff 0xffffffffffcfcfff

def z19 : W := mkw 0x0428216082c10290 0x8810a085820b040a 0x003001c003800000 0x0000c007000e0000

def z20 : W := mkw 0x0fbe3161fbeb8291 0xe83ef8c587efae0a 0xfffff1f1ffffc3ff 0xffffffc7c7ffff0f

def z21 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xfffffffffffc001f 0xfffffffffffff000

def z22 : W := mkw 0x053e000093680000 0xc014f800024da000 0x003f000003fc0010 0x1000fc00000ff000

def z23 : W := mkw 0x1ac1efbc0000003e 0x006b07bef0000000 0xdfc0fffe00000000 0xef7f03fff8000000

def z24 : W := mkw 0x0ffcffebfff3ffb9 0xbc3ff3ffafffcffe 0xfffcfffffff3ffff 0xfffff3ffffffcfff

def z25 : W := mkw 0x0114028800000008 0x0004500a20000000 0xc3340fce00000000 0xfb0cd03f38000000

def z26 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xbc3071c1c3830002 0x42f0c1c7070e0c00

def z27 : W := mkw 0x000010016c02e801 0x3000004005b00ba0 0xfc00f001fc03fc2f 0x67f003c007f00ff0

def z28 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff8031fffcc3ff 0xbfbffe00c7fff30f

def z29 : W := mkw 0x011402c811a10608 0x0404500b20468418 0xc33007c033830f33 0xf30cc01f00ce0c3c

def z30 : W := mkw 0x0a80540168028821 0x302a015005a00a20 0xbf007601f0030c02 0x42fc01d807c00c30

def z31 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff0e01ffff3c3f 0x7fbffc3807fffcf0

def z32 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0x03ff00003ffc0018 0x180ffc0000fff000

def z33 : W := mkw 0x053c02ca93f11708 0x8414f00b2a4fc45c 0xef3c0fcff3f33f3f 0xffbcf03f3fcfccfc

def z34 : W := mkw 0x0000000000000000 0x0000000000000000 0x400880300040c3f5 0xb5002200c001030f

def z35 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc33c8ffe33f3ffff 0xff0cf23ff8cfcfff

def z36 : W := mkw 0x0a80000128000001 0x002a000004a00000 0xefc00001fc00000f 0x0fbf000007f00000

def z37 : W := mkw 0x0ffedc01ff6ae821 0xf03ffb7007fdaba0 0xfffffe01fffffc3f 0x7ffffff807fffff0

def z38 : W := mkw 0x0a80000128000001 0x002a000004a00000 0xefcf0001fc7c001f 0x1fbf3c0007f1f000

def z39 : W := mkw 0x1fffefbc1120003e 0x007fffbef0448000 0xdffffffe33b0001b 0xff7ffffff8cec000

def z40 : W := mkw 0x81558ade15b5774c 0x0605562b7856d5dd 0xc3ff8ffe3fffffff 0xff0ffe3ff8ffffff

def z41 : W := mkw 0x0000316040838290 0x280000c581020e0a 0xfc00f1f1c003c3e7 0xe7f003c7c7000f0f

def z42 : W := mkw 0x1bd7ce9d3928002f 0x406f5f3a74e4a000 0x03c70e0e3c3c0008 0x080f1c3838f0f000

def z43 : W := mkw 0x0041881400000004 0x0001062050000000 0x40cf883e00000000 0xbd033e20f8000000

def z44 : W := mkw 0x0ac1dc156c02e825 0x302b077055b00ba0 0xffcffe3ffc03fc2f 0xffff3ff8fff00ff0

def z45 : W := mkw 0x0eaa0001aa480001 0xc03aa80006a92000 0xecfb0001cfcc0017 0x17b3ec00073f3000

def z46 : W := mkw 0x0114028800000008 0x0004500a20000000 0x833007c000000000 0x420cc01f00000000

def z47 : W := mkw 0x0eaa3121ea4a8091 0xe83aa8c487a92a02 0x3ccbf031cc4cc0c4 0x04f32fc0c7313303

def z48 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xbf00fe01f003fc22 0x62fc03f807c00ff0

def z49 : W := mkw 0x1fbe67a9bb68003b 0xc07ef99ea6eda000 0xffff77c1fffc001f 0x5ffffddf07fff000

def z50 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x1cfff1fe00000000 0x9473ffc7f8000000

def z51 : W := mkw 0x0ee8fd61eec3eab1 0xb83ba3f587bb0faa 0xfcf8f1f1cfc3c3f7 0xf7f3e3c7c73f0f0f

def z52 : W := mkw 0x1eebefbc0000003e 0x007bafbef0000000 0x1ccbfffe00000000 0xe4732ffff8000000

def z53 : W := mkw 0x0b96000139280001 0x402e580004e4a000 0x03c700003c3c0008 0x080f1c0000f0f000

def z54 : W := mkw 0x1469efbc0000003e 0x0051a7bef0000000 0xdc38fffe00000000 0xf770e3fff8000000

def z55 : W := mkw 0x8041881604147144 0x02010620581051c5 0x40cf883e0c3c3008 0xbd033e20f830f0c0

def z56 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x00340fce03b33f30 0xf000d03f380eccfc

def z57 : W := mkw 0x0000004200911700 0x040000010802445c 0x0000000000033f20 0x0000000000000cfc

def z58 : W := mkw 0x0000004000810200 0x0000000100020408 0xc03001c003830333 0xf300c007000e0c0c

def z59 : W := mkw 0x0eaa0001bb680001 0xc03aa80006eda000 0x2ccb0001fffc001f 0x04b32c0007fff000

def z60 : W := mkw 0x0041881400000004 0x0001062050000000 0x40cf883e0c7c001d 0xbd033e20f831f000

def z61 : W := mkw 0x0428216082c10290 0x8810a085820b040a 0x003801f003c003d0 0x9000e007c00f000f

def z62 : W := mkw 0x053c33ead3f39798 0xac14f0cfab4fce5e 0xff3cfffff3f3ffff 0xfffcf3ffffcfcfff

def z63 : W := mkw 0x8041881604147144 0x02010620581051c5 0x00c7080e0c3c3008 0x08031c203830f0c0

def z64 : W := mkw 0x0040dc004402e820 0x3001037001100ba0 0x1000fe000003fc20 0x604003f800000ff0

def z65 : W := mkw 0x1ac1ffbd6c02e83f 0x306b07fef5b00ba0 0xffc0fffffc03fc2f 0xefff03fffff00ff0

def z66 : W := mkw 0x853f0016937c1144 0xc214fc005a4df045 0x003f003e03fc03d0 0x9000fc00f80ff00f

def z67 : W := mkw 0x0428212000000010 0x0010a08480000000 0xdc38f1f000000000 0xf770e3c7c0000000

def z68 : W := mkw 0x1ffffffcc2c382be 0xa87ffffff30b0e0a 0xffffffffc3c3c3f7 0xffffffffff0f0f0f

def z69 : W := mkw 0x1041fffc408382be 0x284107fff1020e0a 0x1000fffe0003c3e0 0xe04003fff8000f0f

def z70 : W := mkw 0x8469b976c6d7f3d4 0xaa11a6e5db1b5fcf 0xfcfff9ffcffff3ff 0xfff3ffe7ff3fffcf

def z71 : W := mkw 0x1fffffbd6c02e83f 0x307ffffef5b00ba0 0xfffffffffc03fc2f 0xfffffffffff00ff0

def z72 : W := mkw 0x8ac1dc176c16f965 0x322b07705db05be5 0xffcffe3ffc7fffff 0xffff3ff8fff1ffff

def z73 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xbc3071c1c3c3c3f7 0x42f0c1c7070f0f0f

def z74 : W := mkw 0x81558a9e1534754c 0x0605562a7854d1d5 0x43cf8e3e3c7cfffd 0xbd0f3e38f8f1f3ff

def z75 : W := mkw 0x0a80540168028821 0x302a015005a00a20 0x3c007001c0000000 0x00f001c007000000

def z76 : W := mkw 0x0fbe02cbbbf91709 0xc43ef80b2eefe45c 0xefff0fcfffff3f3f 0xffbffc3f3ffffcfc

def z77 : W := mkw 0x1041effe0091173e 0x044107bff802445c 0x1000fffe00033f20 0xe04003fff8000cfc

def z78 : W := mkw 0x0000000000000000 0x0000000000000000 0x400080000000c025 0x2500020000000300

def z79 : W := mkw 0x1b9646880000002a 0x006e591a20000000 0x0300060000000000 0x000c001800000000

def z80 : W := mkw 0x0000000128000001 0x0000000004a00000 0x20000001fc00000f 0x0080000007f00000

def z81 : W := mkw 0x04281000c2428000 0xa010a04003090a00 0xfc38f001c3c3c037 0x77f0e3c0070f0f00

def z82 : W := mkw 0x0fbe5401fb6a8821 0xf03ef95007edaa20 0xbf307601f3830c02 0x42fcc1d807ce0c30

def z83 : W := mkw 0x0a80440000000020 0x002a011000000000 0x9f00760000000000 0x427c01d800000000

def z84 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000000000000331 0xb10000000000000c

def z85 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x003401ce03b00310 0x9000d007380ec00c

def z86 : W := mkw 0x000002ca00911708 0x0400000b2802445c 0x00000fce00033f20 0xe000003f38000cfc

def z87 : W := mkw 0x0eaa0001aa480001 0xc03aa80006a92000 0x2ccb0001cc4c0004 0x04b32c0007313000

def z88 : W := mkw 0x0ee8fd21ee42e8b1 0xb83ba3f487b90ba2 0x3cc8f031cc40c0c4 0x04f323c0c7310303

def z89 : W := mkw 0x0000004211b11700 0x040000010846c45c 0xc03001c033b33f3b 0xf300c00700ceccfc

def z90 : W := mkw 0x8041881604147144 0x02010620581051c5 0x0000883e0000f3e0 0xa0000220f80003cf

def z91 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0x3cc0f001cc00c004 0x04f303c007300300

def z92 : W := mkw 0x0000316040838290 0x280000c581020e0a 0x1000f1f00003c3e0 0xe04003c7c0000f0f

def z93 : W := mkw 0x8041881604147144 0x02010620581051c5 0x0000080e00003000 0x00000020380000c0

def z94 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x83300fce33833f22 0xe20cc03f38ce0cfc

def z95 : W := mkw 0x8bd788173d3c7145 0x422f5e205cf4f1c5 0x43cf883e3c7cf3fd 0xbd0f3e20f8f1f3cf

def z96 : W := mkw 0x0040880004006000 0x0001022000100180 0x40c088000c00f02d 0x2d030220003003c0

def z97 : W := mkw 0x1fbe67a80000003a 0x007ef99ea0000000 0x9f3077c000000000 0x427cc1df00000000

def z98 : W := mkw 0x8000000204147140 0x02000000081051c5 0x000000000c7cf3fd 0x000000000031f3cf

def z99 : W := mkw 0x8041881604147144 0x02010620581051c5 0x00c7883e0c3cf3e8 0xa8031e20f830f3cf

def z100 : W := mkw 0x80001042c6d7f3c0 0xaa0000410b1b5fcf 0x20000001cffff3ff 0x00800000073fffcf

def z101 : W := mkw 0x0000004211b11700 0x040000010846c45c 0x0000000003b00310 0x00000000000ec00c

def z102 : W := mkw 0x0000000000000000 0x0000000000000000 0x00cb00000c4c0004 0x04032c0000313000

def z103 : W := mkw 0x0040cc0004006820 0x10010330001001a0 0x00000e0000003c00 0x00000038000000f0

def z104 : W := mkw 0x8041881604147144 0x02010620581051c5 0x0000883e0c7cf3fd 0xa0000220f831f3cf

def z105 : W := mkw 0x0fbe000011200000 0x003ef80000448000 0xcfff000033b0001b 0x1f3ffc0000cec000

def z106 : W := mkw 0x0040880004006000 0x0001022000100180 0x40cf88000c7cf03d 0x3d033e200031f3c0

def z107 : W := mkw 0x0fbe000000000000 0x003ef80000000000 0xcfff000000000000 0x1f3ffc0000000000

def z108 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x03340fce33b03f18 0x980cd03f38cec0fc

def z109 : W := mkw 0x8001001600141144 0x0200040058005045 0x400f803e007cc3f5 0xb5003e00f801f30f

def z110 : W := mkw 0x0fbe2121bb680011 0xc03ef88486eda000 0xfffff1f1fffc001f 0xffffffc7c7fff000

def z111 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xaff70001ffbc000a 0x0abfdc0007fef000

def z112 : W := mkw 0x1bd7ce9c0000002e 0x006f5f3a70000000 0x03c70e0e00000000 0x080f1c3838000000

def z113 : W := mkw 0x1eebed35aa480037 0xc07bafb4d6a92000 0x3ccbf031cc4c0004 0x04f32fc0c7313000

def z114 : W := mkw 0x1fbe67a9bb68003b 0xc07ef99ea6eda000 0xbf3077c1f3800002 0x42fcc1df07ce0000

def z115 : W := mkw 0x8000000204147140 0x02000000081051c5 0x40cf00000c7cf3fd 0x1d033c000031f3cf

def z116 : W := mkw 0x0469a93400000014 0x0011a6a4d0000000 0xdcfff9fe00000000 0xff73ffe7f8000000

def z117 : W := mkw 0x857dbbfed7f7f7dc 0xae15f6effb5fdfdf 0xffffffffffffffff 0xffffffffffffffff

def z118 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0x2cff0001cffc0014 0x14b3fc00073ff000

def z119 : W := mkw 0x0b96000000000000 0x002e580000000000 0x03c7000000000000 0x080f1c0000000000

def z120 : W := mkw 0x00001042d3f39780 0xac0000410b4fce5e 0x20000001f3f3ffff 0x0080000007cfcfff

def z121 : W := mkw 0x0428212000000010 0x0010a08480000000 0x003801f000000000 0x9000e007c0000000

def z122 : W := mkw 0x0114028a11301508 0x0404500a2844c054 0xc3340fce30303c08 0xfb0cd03f38c0c0f0

def z123 : W := mkw 0x0000100168028801 0x3000004005a00a20 0x20000001f0030c02 0x0080000007c00c30

def z124 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000e0000033c20 0x6000003800000cf0

def z125 : W := mkw 0x8001001400040044 0x0200040050001001 0x000b0030004c00c0 0x00002c00c0013003

def z126 : W := mkw 0x800010036c16f941 0x320000400db05be5 0x20000001fc7fffff 0x0080000007f1ffff

def z127 : W := mkw 0x0ac0dc0168028821 0x302b037005a00a20 0xffc0fe01f0030c02 0x6fff03f807c00c30

def z128 : W := mkw 0x0a82000128080001 0x402a080004a02000 0x00c300000c0c0000 0x00030c0000303000

def z129 : W := mkw 0x81558a9e1534754c 0x0605562a7854d1d5 0x03c70e0e3c3c3c08 0x080f1c3838f0f0f0

def z130 : W := mkw 0x0428000082400000 0x8010a00002090000 0xec380001c3c00017 0x17b0e000070f0000

def z131 : W := mkw 0x8fffb977fffff3d5 0xea3ffee5dfffffcf 0xfffff9fffffff3ff 0xffffffe7ffffffcf

def z132 : W := mkw 0x9fffefbe0414717e 0x027fffbef81051c5 0xdffffffe0c7cf3fd 0xff7ffffff831f3cf

def z133 : W := mkw 0x8429217682d513d4 0x8a10a485da0b544f 0x003f01fe03fc03d0 0x9000fc07f80ff00f

def z134 : W := mkw 0x0bd4ce8800000028 0x002f533a20000000 0xdff4ffce00000000 0xff7fd3ff38000000

def z135 : W := mkw 0x0000000200101100 0x0000000008004044 0x4004080e00303339 0xb90010203800c0cc

def z136 : W := mkw 0x0428000082400000 0x8010a00002090000 0xec388031c3c0c3f7 0xb7b0e200c70f030f

def z137 : W := mkw 0x0ea80001aa400001 0x803aa00006a90000 0xeff80001ffc0001f 0x1fbfe00007ff0000

def z138 : W := mkw 0x1ffffffcc2c382be 0xa87ffffff30b0e0a 0xffffffffc3830002 0xffffffffff0e0c00

def z139 : W := mkw 0x0000000000000000 0x0000000000000000 0xc3000e0030033c2b 0x6b0c003800c00cf0

def z140 : W := mkw 0x80419856c6d7f3c4 0xaa0106615b1b5fcf 0x60cf883fcffff3ff 0xbd833e20ff3fffcf

def z141 : W := mkw 0x157fefbc0000003e 0x0055ffbef0000000 0x103ffffe00000000 0xf040fffff8000000

def z142 : W := mkw 0x8bd788173d3c7145 0x422f5e205cf4f1c5 0x03c7080e3c3c3008 0x080f1c2038f0f0c0

def z143 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z144 : W := mkw 0x011402c811a10608 0x0404500b20468418 0x833007c033830c02 0x420cc01f00ce0c30

def z145 : W := mkw 0x0000104040838280 0x2800004101020e0a 0x000000000003c3e0 0x0000000000000f0f

def z146 : W := mkw 0x8041b9764497f3d4 0x2a0106e5d9125fcf 0x50cff9fe0c7ff3fd 0xfd433fe7f831ffcf

def z147 : W := mkw 0x0040dc004402e820 0x3001037001100ba0 0xfc00fe01c003fc27 0x67f003f807000ff0

def z148 : W := mkw 0x053c23ea11b11718 0x0414f08fa846c45c 0xdf3cfffe33b33f3b 0xff7cf3fff8ceccfc

def z149 : W := mkw 0x00000001bb680001 0xc000000006eda000 0x20000001fffc001f 0x0080000007fff000

def z150 : W := mkw 0x1155efbc0000003e 0x004557bef0000000 0xd334fffe00000000 0xfb4cd3fff8000000

def z151 : W := mkw 0x00001041eec3ea81 0xb800004107bb0faa 0x20000001ffc3ffff 0x0080000007ff0fff

def z152 : W := mkw 0x0000000139280001 0x4000000004e4a000 0x000000003c3c0008 0x0000000000f0f000

def z153 : W := mkw 0x0114000211301100 0x000450000844c044 0xc334080e33b0333b 0xbb0cd02038cec0cc

def z154 : W := mkw 0x1fffffbdff6ae83f 0xf07ffffef7fdaba0 0xfffffffffffffc3f 0xfffffffffffffff0

def z155 : W := mkw 0x1fffefbe1130153e 0x047fffbef844c054 0xdffffffe30303c08 0xff7ffffff8c0c0f0

def z156 : W := mkw 0x0eaa000000000000 0x003aa80000000000 0x0ccb000000000000 0x04332c0000000000

def z157 : W := mkw 0x142b213400000016 0x0050ac84d0000000 0x000b003000000000 0x00002c00c0000000

def z158 : W := mkw 0x1fffeffe11b1173e 0x047fffbff846c45c 0xdffffffe33b33f3b 0xff7ffffff8ceccfc

def z159 : W := mkw 0x153f23bc0000001e 0x0054fc8ef0000000 0xdc3ff1fe00000000 0xf770ffc7f8000000

def z160 : W := mkw 0x000010016c02e801 0x3000004005b00ba0 0x20000001fc03fc2f 0x0080000007f00ff0

def z161 : W := mkw 0x153f23bc0000001e 0x0054fc8ef0000000 0x003f01fe00000000 0x9000fc07f8000000

def z162 : W := mkw 0x8041881604147144 0x02010620581051c5 0x40cf080e0c7c301d 0x1d033c203831f0c0

def z163 : W := mkw 0x053e3160d3eb8290 0xe814f8c5834fae0a 0xfc3ff1f1c3ffc3f7 0xf7f0ffc7c70fff0f

def z164 : W := mkw 0x0001001400000004 0x0000040050000000 0x000f003e00000000 0x90003c00f8000000

def z165 : W := mkw 0x0000000000000000 0x0000000000000000 0x4008803000000000 0xb5002200c0000000

def z166 : W := mkw 0x04283120c2428090 0xa810a0c483090a02 0xfc08f031c043c0e7 0x67f023c0c7010f03

def z167 : W := mkw 0x0000000200101100 0x0000000008004044 0x0000000000303339 0x000000000000c0cc

def z168 : W := mkw 0x0000100040028000 0x2000004001000a00 0xfc00f001c003c027 0x67f003c007000f00

def z169 : W := mkw 0x0ee8fd61eec3eab1 0xb83ba3f587bb0faa 0xfff8fff1ffc3ffff 0xffffe3ffc7ff0fff

def z170 : W := mkw 0x0114000011200000 0x0004500000448000 0x0304000030300008 0x080c100000c0c000

def z171 : W := mkw 0x0000316040838290 0x280000c581020e0a 0xd030f1f00383c3f3 0xf340c3c7c00e0f0f

def z172 : W := mkw 0x053e216093e90290 0xc814f885824fa40a 0x003f01f003fc03d0 0x9000fc07c00ff00f

def z173 : W := mkw 0x00001040c2c38280 0xa8000041030b0e0a 0x20000001c3c3c3f7 0x00800000070f0f0f

def z174 : W := mkw 0x1ffffffdfbeb82bf 0xe87ffffff7efae0a 0xffffffffffffc3ff 0xffffffffffffff0f

def z175 : W := mkw 0x0b96000139280001 0x402e580004e4a000 0x0300000030000000 0x000c000000c00000

def z176 : W := mkw 0x0ac0dc0040028020 0x202b037001000a00 0xffc0fe01c003c027 0x6fff03f807000f00

def z177 : W := mkw 0x0428000082400000 0x8010a00002090000 0xecff0001cffc001f 0x1fb3fc00073ff000

def z178 : W := mkw 0x0bd6cc013d286821 0x502f5b3004f4a1a0 0x03c70e003c3c3c08 0x080f1c3800f0f0f0

def z179 : W := mkw 0x0468b960c6c3e290 0xa811a2e5831b0f8a 0xfcf8f9f1cfc3f3ff 0xfff3e3e7c73f0fcf

def z180 : W := mkw 0x0fbe000000000000 0x003ef80000000000 0x8f30000000000000 0x023cc00000000000

def z181 : W := mkw 0x0114028811200008 0x0004500a20448000 0xc3340fce33b0001b 0xfb0cd03f38cec000

def z182 : W := mkw 0x0ffedc01ff6ae821 0xf03ffb7007fdaba0 0xfffff001fffcc01f 0x1fffffc007fff300

def z183 : W := mkw 0x1fffeffe0091173e 0x047fffbff802445c 0xdffffffe00033f20 0xff7ffffff8000cfc

def z184 : W := mkw 0x053c000093600000 0x8014f000024d8000 0xef3c0001f3f0001f 0x1fbcf00007cfc000

def z185 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x833407ce33b30f12 0xd20cd01f38cecc3c

def z186 : W := mkw 0x0bd4decb7db3ff29 0x342f537b2df6cffc 0xfff4ffcfffb3ff3f 0xffffd3ff3ffecffc

def z187 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xbc38f1f1c3c3c0c6 0x46f0e3c7c70f0f03

def z188 : W := mkw 0x1eebed3400000036 0x007bafb4d0000000 0x5ccff83e00000000 0xbd733fe0f8000000

def z189 : W := mkw 0x8041881604147144 0x02010620581051c5 0x00cf083e0c7c33d8 0x98033c20f831f0cf

def z190 : W := mkw 0x0114028a11301508 0x0404500a2844c054 0xc3040e0e30333c2b 0x6b0c103838c0ccf0

def z191 : W := mkw 0x8041881604147144 0x02010620581051c5 0x00c7080e0c7cf3fd 0x08031c203831f3cf

def z192 : W := mkw 0x8040880204147140 0x02010220081051c5 0x40c088000c7cf3fd 0x2d0302200031f3cf

def z193 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xaf300001f3800002 0x02bcc00007ce0000

def z194 : W := mkw 0x8ac1dc156c06e865 0x322b077055b01ba1 0xffcbfe31fc4ffcef 0x6fff2ff8c7f13ff3

def z195 : W := mkw 0x0ac0cc0000000020 0x002b033000000000 0x03c00e0000000000 0x080f003800000000

def z196 : W := mkw 0x0ac0cc0000000020 0x002b033000000000 0xdfc0fe0000000000 0x6f7f03f800000000

def z197 : W := mkw 0x000010016c02e801 0x3000004005b00ba0 0xe3000e01fc03fc2f 0x6b8c003807f00ff0

def z198 : W := mkw 0x8000000204147140 0x02000000081051c5 0x4004080e0c7cf3fd 0xb90010203831f3cf

def z199 : W := mkw 0x0ac0cc0128000021 0x002b033004a00000 0xffc0fe01fc00000f 0x6fff03f807f00000

def z200 : W := mkw 0x0000004000810200 0x0000000100020408 0x000001c000030320 0xe000000700000c0c

def z201 : W := mkw 0x0428216082c10290 0x8810a085820b040a 0xdc38f1f003c003d0 0xf770e3c7c00f000f

def z202 : W := mkw 0x80418817bf7c7145 0xc20106205efdf1c5 0x60cf883ffffcf3ff 0xbd833e20fffff3cf

def z203 : W := mkw 0x04283120c2428090 0xa810a0c483090a02 0x3c08f031c040c0c4 0x04f023c0c7010303

def z204 : W := mkw 0x8001001600141144 0x0200040058005045 0x0000003e000003c0 0x80000000f800000f

def z205 : W := mkw 0x0428216000810210 0x0010a08580020408 0xdc38f1f003830333 0xf770e3c7c00e0c0c

def z206 : W := mkw 0x80418ade0495774c 0x0601062b781255dd 0x00008ffe0003ffe0 0xe000023ff8000fff

def z207 : W := mkw 0x100123bc0000001e 0x0040048ef0000000 0x000001fe00000000 0x80000007f8000000

def z208 : W := mkw 0x0000100040028000 0x2000004001000a00 0xff00fe01f003fc2f 0x6ffc03f807c00ff0

def z209 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xff38fff1f3c3ffff 0xfffce3ffc7cf0fff

def z210 : W := mkw 0x1fbe77a96802883b 0x307ef9dea5a00a20 0xbf3077c1f0030c02 0x42fcc1df07c00c30

def z211 : W := mkw 0x0b9602cb39b91709 0x442e580b2ce6e45c 0xc3f70fce3fbf3f3b 0xfb0fdc3f38fefcfc

def z212 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0x2fcf0001fc7c000c 0x0cbf3c0007f1f000

def z213 : W := mkw 0x053e02ca93f91708 0xc414f80b2a4fe45c 0x003f01ce03fc0310 0x9000fc07380ff00c

def z214 : W := mkw 0x0a800001bb680001 0xc02a000006eda000 0xefc00001fffc001f 0x0fbf000007fff000

def z215 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0x3c38f1f1c3c0c3d4 0x94f0e3c7c70f030f

def z216 : W := mkw 0x8ac1dc176c16f965 0x322b07705db05be5 0x7ccff83fcc7cf3fd 0xbdf33fe0ff31f3cf

def z217 : W := mkw 0x8eeb8817ae5c7145 0xc23bae205eb971c5 0x6ccf883fcc7cf3fd 0xbdb33e20ff31f3cf

def z218 : W := mkw 0x1eebfd74c2c382b6 0xa87baff5d30b0e0a 0xfcfbf1f1c3c3c3f7 0xf7f3efc7c70f0f0f

def z219 : W := mkw 0x1fbf67bc0000003e 0x007efd9ef0000000 0x9f3f77fe00000000 0xd27cfddff8000000

def z220 : W := mkw 0x0116000011280000 0x400458000044a000 0x00070000003c0000 0x00001c000000f000

def z221 : W := mkw 0x8001001600141144 0x0200040058005045 0x000f003e007c03d0 0x90003c00f801f00f

def z222 : W := mkw 0x000002ca11b11708 0x0400000b2846c45c 0x00000fce33b33f3b 0xe000003f38ceccfc

def z223 : W := mkw 0x053c23a800000018 0x0014f08ea0000000 0xdf3cfffe00000000 0xff7cf3fff8000000

def z224 : W := mkw 0x0154deca55b3ff28 0x3405537b2956cffc 0xd334ffce33b3ff3b 0xfb4cd3ff38cecffc

def z225 : W := mkw 0x0ac1cc1400000024 0x002b073050000000 0xdfcffe3e00000000 0xff7f3ff8f8000000

def z226 : W := mkw 0x000002ca00911708 0x0400000b2802445c 0x40040fce00333f39 0xf900103f3800ccfc

def z227 : W := mkw 0x0000316040838290 0x280000c581020e0a 0x5008f1f00043c3f5 0xf54023c7c0010f0f

def z228 : W := mkw 0x0114028811200408 0x0404500a20448010 0x0300060030000c00 0x000c001800c00030

def z229 : W := mkw 0x0b96028b39381509 0x442e580a2ce4e054 0x03c70e0e3c3c3c08 0x080f1c3838f0f0f0

def z230 : W := mkw 0x0ffefd61ffebeab1 0xf83ffbf587ffafaa 0xfffffff1ffffffff 0xffffffffc7ffffff

def z231 : W := mkw 0x153f23fc82c1029e 0x8854fc8ff20b040a 0x003f01fe03c003d0 0x9000fc07f80f000f

def z232 : W := mkw 0x953f23be0014115e 0x0254fc8ef8005045 0x003f01fe007c03d0 0x9000fc07f801f00f

def z233 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe30033c2b 0xff7ffffff8c00cf0

def z234 : W := mkw 0x8041881404046044 0x0201062050101181 0x00cb80300c4cc0c4 0x04032e00c0313303

def z235 : W := mkw 0x0bd4cecb3db17f29 0x142f533b2cf6c5fc 0xc3f40fce3fb33f3b 0xfb0fd03f38feccfc

def z236 : W := mkw 0x0fbe3161fbeb8291 0xe83ef8c587efae0a 0xff38f1f1f3c3c3f7 0xf7fce3c7c7cf0f0f

def z237 : W := mkw 0x8fff8815bf6c6045 0xc23ffe2056fdb181 0xefff8031fffcc0df 0x1fbffe00c7fff303

def z238 : W := mkw 0x000000012c006801 0x1000000004b001a0 0x000000003c003c08 0x0000000000f000f0

def z239 : W := mkw 0x0000000000000000 0x0000000000000000 0x8300060030030c02 0x420c001800c00c30

def z240 : W := mkw 0x0fbe3160c2c38290 0xa83ef8c5830b0e0a 0xfffff1f1c3c3c3f7 0xffffffc7c70f0f0f

def z241 : W := mkw 0x04283120c2428090 0xa810a0c483090a02 0xfc38f031c3c0c0d7 0x17f0e3c0c70f0303

def z242 : W := mkw 0x0fbe000139280001 0x403ef80004e4a000 0xcfff00003c3c0008 0x1f3ffc0000f0f000

def z243 : W := mkw 0x0000540040028820 0x3000015001000a20 0x1000760000030c00 0x404001d800000c30

def z244 : W := mkw 0x0000100040028000 0x2000004001000a00 0xbc007001c0030002 0x42f001c007000c00

def z245 : W := mkw 0x0040cc0000000020 0x0001033000000000 0x1000fe0000000000 0x604003f800000000

def z246 : W := mkw 0x000002ca00911708 0x0400000b2802445c 0xc3000fce30033f2b 0xeb0c003f38c00cfc

def z247 : W := mkw 0x0fbe02cbbbf91709 0xc43ef80b2eefe45c 0xef340fcff3b33f3b 0xfbbcd03f3fceccfc

def z248 : W := mkw 0x0bd4ce8b3d307d29 0x142f533a2cf4c1f4 0x03c40e0e3c303c08 0x080f103838f0c0f0

def z249 : W := mkw 0x04280001bb680001 0xc010a00006eda000 0xec380001fffc001f 0x17b0e00007fff000

def z250 : W := mkw 0x8ac0dc036c16f961 0x322b03700db05be5 0xffc0fe01fc7fffff 0x6fff03f807f1ffff

def z251 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc38f1f1c3830002 0xf7f0e3c7c70e0c00

def z252 : W := mkw 0x0ac0cc012c006821 0x102b033004b001a0 0x03c00e003c003c08 0x080f003800f000f0

def z253 : W := mkw 0x9fffefbfbf7c717f 0xc27fffbefefdf1c5 0xfffffffffffcf3ff 0xfffffffffffff3cf

def z254 : W := mkw 0x0114004211b11700 0x040450010846c45c 0xc334000033b33f3b 0x1b0cd00000ceccfc

def z255 : W := mkw 0x0000000211301500 0x040000000844c054 0x0000000030303c08 0x0000000000c0c0f0

def z256 : W := mkw 0x0ac0cc0000000020 0x002b033000000000 0x1cc0f00000000000 0x047303c000000000

def z257 : W := mkw 0x1fffffbc4402e83e 0x307ffffef1100ba0 0xdffffffe0003fc20 0xff7ffffff8000ff0

def z258 : W := mkw 0x0040dc004402e820 0x3001037001100ba0 0xd300fe003003fc2b 0x6b4c03f800c00ff0

def z259 : W := mkw 0x0428000000000000 0x0010a00000000000 0xcc38000000000000 0x1730e00000000000

def z260 : W := mkw 0x8041881600141144 0x0201062058005045 0x40cf883e007c03d0 0xbd033e20f801f00f

def z261 : W := mkw 0x0fbe02c9bbe90609 0xc43ef80b26efa418 0xaf3007c1f3830c02 0x42bcc01f07ce0c30

def z262 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xaffb0001ffcc0006 0x06bfec0007ff3000

def z263 : W := mkw 0x0a80000128000001 0x002a000004a00000 0xaf000001f0000002 0x02bc000007c00000

def z264 : W := mkw 0x8001001600141144 0x0200040058005045 0x40cf003e0c7c03dd 0x9d033c00f831f00f

def z265 : W := mkw 0x011402cbbbf91709 0xc404500b2eefe45c 0xe3340fcfffff3f3f 0xfb8cd03f3ffffcfc

def z266 : W := mkw 0x000010437db3ff01 0x340000410df6cffc 0x20000001ffb3ff3f 0x0080000007fecffc

def z267 : W := mkw 0x0428000082400000 0x8010a00002090000 0x0038000003c00010 0x1000e000000f0000

def z268 : W := mkw 0x811402ca15b57748 0x0604500b2856d5dd 0xc3340fce3fffffff 0xfb0cd03f38ffffff

def z269 : W := mkw 0x0114028a11301508 0x0404500a2844c054 0x03040e0e30303c08 0x080c103838c0c0f0

def z270 : W := mkw 0x1fffeffc82c102be 0x887fffbff20b040a 0xdffffffe03c003d0 0xff7ffffff80f000f

def z271 : W := mkw 0x0000000082400000 0x8000000002090000 0x20000001c3c00017 0x00800000070f0000

def z272 : W := mkw 0x8fff8817bf7c7145 0xc23ffe205efdf1c5 0xefff883ffffcf3ff 0xbfbffe20fffff3cf

def z273 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc8fe31fc43ffff 0xffff23f8c7f10fff

def z274 : W := mkw 0x0000000200101100 0x0000000008004044 0x400c883e0070f3fd 0xbd003220f801c3cf

def z275 : W := mkw 0x8041881604147144 0x02010620581051c5 0x00cb883e0c4cf3e4 0xa4032e20f83133cf

def z276 : W := mkw 0x00001041fbeb8281 0xe800004107efae0a 0x20000001ffffc3ff 0x0080000007ffff0f

def z277 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0x50cffffe00000000 0xfd433ffff8000000

def z278 : W := mkw 0x1fffeffc0081023e 0x007fffbff0020408 0xdffffffe03830333 0xff7ffffff80e0c0c

def z279 : W := mkw 0x8041881604147144 0x02010620581051c5 0x00cf803e0c7cc3d4 0x94033e00f831f30f

def z280 : W := mkw 0x8041881404046044 0x0201062050101181 0x000080300000c0c0 0x00000200c0000303

def z281 : W := mkw 0x1ffffffc408382be 0x287ffffff1020e0a 0xdffffffe0003c3e0 0xff7ffffff8000f0f

def z282 : W := mkw 0x1eebfd34c24280b6 0xa87baff4d3090a02 0x3ccbf031c040c0c4 0x04f32fc0c7010303

def z283 : W := mkw 0x011402c811a10608 0x0404500b20468418 0xc33407c033b30c1b 0x5b0cd01f00cecc30

def z284 : W := mkw 0x1fffefffbbf9173f 0xc47fffbffeefe45c 0xffffffffffff3f3f 0xfffffffffffffcfc

def z285 : W := mkw 0x80000003bf7c7141 0xc20000000efdf1c5 0x20000001fffcf3ff 0x0080000007fff3cf

def z286 : W := mkw 0x0ac0cc012c006821 0x102b033004b001a0 0xc3c00e003c033c2b 0x6b0f003800f00cf0

def z287 : W := mkw 0x8041881604147144 0x02010620581051c5 0x40c7880e0c3cf02d 0x2d031e203830f3c0

def z288 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x9f30fffe00000000 0xe27cc3fff8000000

def z289 : W := mkw 0x00001040c2c38280 0xa8000041030b0e0a 0x60088031c3c3c3f7 0xb5802200c70f0f0f

def z290 : W := mkw 0x9eebed3604147176 0x027bafb4d81051c5 0x5ccff83e0c7cf3fd 0xbd733fe0f831f3cf

def z291 : W := mkw 0x0041881400000004 0x0001062050000000 0x00c7080e00000000 0x08031c2038000000

def z292 : W := mkw 0x0ee8fd61eec3eab1 0xb83ba3f587bb0faa 0xfff0ffc1ff83fc2f 0x6fffc3ff07fe0ff0

def z293 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0x203801f1c3c3c3f7 0x9080e007c70f0f0f

def z294 : W := mkw 0x0040880000000000 0x0001022000000000 0x40c0880000000000 0x2d03022000000000

def z295 : W := mkw 0x8fbf0017bb7c1145 0xc23efc005eedf045 0xefff003ffffc03df 0x9fbffc00fffff00f

def z296 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x83340fce33b33c0a 0x4a0cd03f38ceccf0

def z297 : W := mkw 0x0fbe3121fb6a8091 0xe83ef8c487edaa02 0xfffff031fffcc0df 0x1fffffc0c7fff303

def z298 : W := mkw 0x0a8054016c02e821 0x302a015005b00ba0 0xbf007601fc03fc2f 0x42fc01d807f00ff0

def z299 : W := mkw 0x81558ade15b5774c 0x0605562b7856d5dd 0x40ff89fe0ffcf3fd 0xbd03fe27f83ff3cf

def z300 : W := mkw 0x0ee8fd216c02e831 0x303ba3f485b00ba0 0xfff8fff1fc03fc2f 0xffffe3ffc7f00ff0

def z301 : W := mkw 0x011402ca00911708 0x0404500b2802445c 0xc3340fce00033f20 0xfb0cd03f38000cfc

def z302 : W := mkw 0x1fbe77e8c2c382ba 0xa87ef9dfa30b0e0a 0xff38f7f1c3c3c3f7 0xf7fce3dfc70f0f0f

def z303 : W := mkw 0x0fbe028bbb781509 0xc43ef80a2eede054 0xefff0e0ffffc3c1f 0x1fbffc383ffff0f0

def z304 : W := mkw 0x011412cb7db3ff09 0x3404504b2df6cffc 0xe3340fcfffb3ff3f 0xfb8cd03f3ffecffc

def z305 : W := mkw 0x0ffe8801bf686001 0xc03ffa2006fda180 0xefff8801fffcf03f 0x3fbffe2007fff3c0

def z306 : W := mkw 0x0428000082400000 0x8010a00002090000 0x2c080001c0400004 0x04b0200007010000

def z307 : W := mkw 0x0a80000128000001 0x002a000004a00000 0x2cc00001cc000004 0x04b3000007300000

def z308 : W := mkw 0x0fbe02c9bbe90609 0xc43ef80b26efa418 0xefff07c1ffff0c1f 0x5fbffc1f07fffc30

def z309 : W := mkw 0x1fffed3400000036 0x007fffb4d0000000 0xdffff03000000000 0x1f7fffc0c0000000

def z310 : W := mkw 0x1fbe67a80000003a 0x007ef99ea0000000 0xdf347fce00000000 0xfb7cd1ff38000000

def z311 : W := mkw 0x0fbe1001fb6a8001 0xe03ef84007edaa00 0xfffff001ffffc03f 0x7fffffc007ffff00

def z312 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xfffffffff3800002 0xffffffffffce0000

def z313 : W := mkw 0x1fffefbd2c00683f 0x107fffbef4b001a0 0xdffffffe3c003c08 0xff7ffffff8f000f0

def z314 : W := mkw 0x1fffce9c0000002e 0x007fff3a70000000 0xcfff0e0e00000000 0x1f3ffc3838000000

def z315 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe0c7c001d 0xff7ffffff831f000

def z316 : W := mkw 0x0000000093680000 0xc0000000024da000 0x0000000003fc0010 0x00000000000ff000

def z317 : W := mkw 0x8041dc164416f964 0x3201077059105be5 0x1000fe3e0003ffe0 0xe04003f8f8000fff

def z318 : W := mkw 0x0ee8fd21ee42e8b1 0xb83ba3f487b90ba2 0xffc8fe31fc43fcef 0x6fff23f8c7f10ff3

def z319 : W := mkw 0x0000000200101100 0x0000000008004044 0x0000080e00003320 0xa0000020380000cc

def z320 : W := mkw 0x0000312040028090 0x280000c481000a02 0x1000f0300000c0c0 0x004003c0c0000303

def z321 : W := mkw 0x0041881600101104 0x0001062058004044 0x40cf883e00303339 0xbd033e20f800c0cc

def z322 : W := mkw 0x011412ca51b39708 0x2404504b2946ce5c 0xff34ffcff3b3ff3f 0xfffcd3ff3fcecffc

def z323 : W := mkw 0x0fbe02ca11b11708 0x043ef80b2846c45c 0xcfff0fce33b33f3b 0xff3ffc3f38ceccfc

def z324 : W := mkw 0x8ac1dc176c16f965 0x322b07705db05be5 0xffc0fe3ffc03ffef 0xefff03f8fff00fff

def z325 : W := mkw 0x9bd7ce9e0414716e 0x026f5f3a781051c5 0x03c70e0e0c3c3008 0x080f1c383830f0c0

def z326 : W := mkw 0x053e000093680000 0xc014f800024da000 0xec3f0001c3fc0017 0x17b0fc00070ff000

def z327 : W := mkw 0x8041881404046044 0x0201062050101181 0x00c300000c0c0000 0x00030c0000303000

def z328 : W := mkw 0x0114028800000008 0x0004500a20000000 0x003401ce00000000 0x9000d00738000000

def z329 : W := mkw 0x0428212082400090 0x8810a08482090002 0x00080030004000c0 0x00002000c0010003

def z330 : W := mkw 0x0fbe028800000008 0x003ef80a20000000 0xcfff0fce00000000 0xff3ffc3f38000000

def z331 : W := mkw 0x8041881404046044 0x0201062050101181 0x40cf80300c7cc0dd 0x1d033e00c031f303

def z332 : W := mkw 0x0040fd604483eab0 0x380103f581120faa 0x1000fff00003ffe0 0xe04003ffc0000fff

def z333 : W := mkw 0x0fbe000093680000 0xc03ef800024da000 0xcfff000003fc0010 0x1f3ffc00000ff000

def z334 : W := mkw 0x053c33e8d3e38698 0xac14f0cfa34f8e1a 0xbf3077c1f3830c02 0x42fcc1df07ce0c30

def z335 : W := mkw 0x0ac0cc012c006821 0x102b033004b001a0 0x43c08e003c00fc2d 0x2d0f023800f003f0

def z336 : W := mkw 0x1fffefbdaa48003f 0xc07fffbef6a92000 0xffffffffcc4c0004 0xffffffffff313000

def z337 : W := mkw 0x8041b9764497f3d4 0x2a0106e5d9125fcf 0x1000f9fe0003f3e0 0xe04003e7f8000fcf

def z338 : W := mkw 0x0a80000000000000 0x002a000000000000 0xcfc0000000000000 0x0f3f000000000000

def z339 : W := mkw 0x0b9456cb79b39f29 0x342e515b2de6ce7c 0xff347fcff3b33f3b 0xfbfcd1ff3fceccfc

def z340 : W := mkw 0x8041881604147144 0x02010620581051c5 0x4004883e0030f3f9 0xb9001220f800c3cf

def z341 : W := mkw 0x00001040c2c38280 0xa8000041030b0e0a 0xe03001c1c3c3c3f7 0xf380c007070f0f0f

def z342 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc3071c1c3830333 0xf3f0c1c7070e0c0c

def z343 : W := mkw 0x011402c800810208 0x0004500b20020408 0xc3340fce03830333 0xfb0cd03f380e0c0c

def z344 : W := mkw 0x8041881604147144 0x02010620581051c5 0xc3cf8e3e3c7fffff 0xff0f3e38f8f1ffff

def z345 : W := mkw 0x0000028800000008 0x0000000a20000000 0x00000fce00000000 0xe000003f38000000

def z346 : W := mkw 0x0000000000000000 0x0000000000000000 0x40cf80300c7cc3fd 0xbd033e00c031f30f

def z347 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff0001f3800002 0x1fbffc0007ce0000

def z348 : W := mkw 0x1fffefbd3928003f 0x407fffbef4e4a000 0xdffffffe3c3c0008 0xff7ffffff8f0f000

def z349 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x9ff77fce00000000 0x4a7fddff38000000

def z350 : W := mkw 0x0000000000000000 0x0000000000000000 0x000f0000007c0010 0x10003c000001f000

def z351 : W := mkw 0x0fff881400000004 0x003ffe2050000000 0xcfff883e00000000 0xbf3ffe20f8000000

def z352 : W := mkw 0x8041885604957344 0x02010621581255cd 0xc0ff89fe0ffff3ff 0xff03fe27f83fffcf

def z353 : W := mkw 0x0114000011200000 0x0004500000448000 0x0034000003b00010 0x1000d000000ec000

def z354 : W := mkw 0x0428000082400000 0x8010a00002090000 0xac300001c3800002 0x02b0c000070e0000

def z355 : W := mkw 0x1bd7ce9c0000002e 0x006f5f3a70000000 0x43cf8e3e00000000 0xbd0f3e38f8000000

def z356 : W := mkw 0x957fabbe0414715e 0x0255feaef81051c5 0x40ff89fe0c7cf3fd 0xbd03fe27f831f3cf

def z357 : W := mkw 0x8ac1dc156c06e865 0x322b077055b01ba1 0x3ccbf031cc4cc0c4 0x04f32fc0c7313303

def z358 : W := mkw 0x8eeb8815ae4c6045 0xc23bae2056b93181 0x2ccb8031cc4cc0c4 0x04b32e00c7313303

def z359 : W := mkw 0x0000000000000000 0x0000000000000000 0x03000e0030003c08 0x080c003800c000f0

def z360 : W := mkw 0x0bd4ceca11b11728 0x042f533b2846c45c 0xdff4ffce33b33f3b 0xff7fd3ff38ceccfc

def z361 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x403409ce03b03339 0xb900d027380ec0cc

def z362 : W := mkw 0x1fffffbd6802883f 0x307ffffef5a00a20 0xfffffffff0030c02 0xffffffffffc00c30

def z363 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0x7cc0f801cc00f02d 0x2df303e0073003c0

def z364 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x03040e0e33b33f3b 0x080c103838ceccfc

def z365 : W := mkw 0x8000000200141140 0x0200000008005045 0x00000000007c03d0 0x000000000001f00f

def z366 : W := mkw 0x0ac0cc0004006020 0x002b033000100180 0xdfc0fe000c00f02d 0x6f7f03f8003003c0

def z367 : W := mkw 0x0000212000000010 0x0000008480000000 0x1000f1f000000000 0xe04003c7c0000000

def z368 : W := mkw 0x0ffecc01bb680021 0xc03ffb3006eda000 0xfffffe01fffc001f 0x7ffffff807fff000

def z369 : W := mkw 0x0114000011200000 0x0004500000448000 0x8330000033800002 0x020cc00000ce0000

def z370 : W := mkw 0x0428216082c10290 0x8810a085820b040a 0xec3801f1c3c003d7 0x97b0e007c70f000f

def z371 : W := mkw 0x0040deca4493ff28 0x3401037b29124ffc 0x1000ffce0003ff20 0xe04003ff38000ffc

def z372 : W := mkw 0x0114000000000000 0x0004500000000000 0xc334000000000000 0x1b0cd00000000000

def z373 : W := mkw 0x9041efbe0414717e 0x024107bef81051c5 0x50cffffe0c7cf3fd 0xfd433ffff831f3cf

def z374 : W := mkw 0x1155effe11b1173e 0x044557bff846c45c 0xd334fffe33b33f3b 0xfb4cd3fff8ceccfc

def z375 : W := mkw 0x0040880004006000 0x0001022000100180 0x00c080000c00c004 0x0403020000300300

def z376 : W := mkw 0x1bd7ce9c0000002e 0x006f5f3a70000000 0xdfc7fe0e00000000 0x6f7f1ff838000000

def z377 : W := mkw 0x011402c811a10608 0x0404500b20468418 0xc3300fc033833c2b 0x6b0cc03f00ce0cf0

def z378 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0x23c00e01fc03fc2f 0x088f003807f00ff0

def z379 : W := mkw 0x8000000204147140 0x02000000081051c5 0x000000000c3c3008 0x000000000030f0c0

def z380 : W := mkw 0x1fbf23bdbb68001f 0xc07efc8ef6eda000 0xefff01fffffc001f 0x9fbffc07fffff000

def z381 : W := mkw 0x04283161fbeb8291 0xe810a0c587efae0a 0xfc38f1f1ffffc3ff 0xf7f0e3c7c7ffff0f

def z382 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xbfc07e01fc033c0a 0x4aff01f807f00cf0

def z383 : W := mkw 0x8469b976c6d7f3d4 0xaa11a6e5db1b5fcf 0xfc38f9ffc3c3f3f7 0xf7f0e3e7ff0f0fcf

def z384 : W := mkw 0x1bd7ce9c0000002e 0x006f5f3a70000000 0xc3f70fce00000000 0xfb0fdc3f38000000

def z385 : W := mkw 0x8001001600141144 0x0200040058005045 0x400f083e007c33f9 0xb9003c20f801f0cf

def z386 : W := mkw 0x0114028a11301508 0x0404500a2844c054 0xc3340e0e33b03c1b 0x1b0cd03838cec0f0

def z387 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfcfff1f1cfffc3ff 0xfff3ffc7c73fff0f

def z388 : W := mkw 0x0000000200101100 0x0000000008004044 0x0004000e00300310 0x900010003800c00c

def z389 : W := mkw 0x0000000000000000 0x0000000000000000 0xec000001c0000007 0x07b0000007000000

def z390 : W := mkw 0x0000004000810200 0x0000000100020408 0x003001c003800310 0x9000c007000e000c

def z391 : W := mkw 0x04281040c2c38280 0xa810a041030b0e0a 0xec380001c3c3c3f7 0x17b0e000070f0f0f

def z392 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000080000003029 0x29000020000000c0

def z393 : W := mkw 0x0ac0decb6c93ff29 0x342b037b2db24ffc 0xffc0ffcffc03ff2f 0xefff03ff3ff00ffc

def z394 : W := mkw 0x0000100040028000 0x2000004001000a00 0x20000001c003c027 0x0080000007000f00

def z395 : W := mkw 0x0fbe2161bbe90291 0xc83ef88586efa40a 0xefff01f1fffc03df 0x9fbffc07c7fff00f

def z396 : W := mkw 0x0eeadc01ee4ae821 0xf03bab7007b92ba0 0x3ccbf001cc4cc004 0x04f32fc007313300

def z397 : W := mkw 0x0eaa0001aa480001 0xc03aa80006a92000 0x2c000001c0000000 0x00b0000007000000

def z398 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe0040c3f5 0xff7ffffff801030f

def z399 : W := mkw 0x857f8816977c7144 0xc215fe205a5df1c5 0x40ff883e0ffcf3fd 0xbd03fe20f83ff3cf

def z400 : W := mkw 0x000002ca00911708 0x0400000b2802445c 0xc0300fce03833f33 0xf300c03f380e0cfc

def z401 : W := mkw 0x0000000000000000 0x0000000000000000 0xc03001c000000000 0xf300c00700000000

def z402 : W := mkw 0x0fbe0003bb781101 0xc03ef8000eede044 0xefff080ffffc333f 0xbfbffc203ffff0cc

def z403 : W := mkw 0x0b960001bb680001 0xc02e580006eda000 0x23c70001fffc001f 0x088f1c0007fff000

def z404 : W := mkw 0x0fbe0041bbe90201 0xc03ef80106efa408 0xefff01c1ffff033f 0xffbffc0707fffc0c

def z405 : W := mkw 0x053c33ead3f39798 0xac14f0cfab4fce5e 0xff347fcff3b33f3b 0xfbfcd1ff3fceccfc

def z406 : W := mkw 0x0428004082c10200 0x8010a001020b0408 0xec3801c1c3c30337 0xf7b0e007070f0c0c

def z407 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc03401ce03b30333 0xf300d007380ecc0c

def z408 : W := mkw 0x0bd6dc017d2ae821 0x702f5b7005f4aba0 0xffc7fe01fc3ffc2f 0x6fff1ff807f0fff0

def z409 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0x3fc0fe01fc00fc0c 0x0cff03f807f003f0

def z410 : W := mkw 0x804198164416f144 0x2201066059105bc5 0xfccff83fcc7ff3ff 0xfff33fe0ff31ffcf

def z411 : W := mkw 0x804198176c16f945 0x320106605db05be5 0x60cf883ffc7fffff 0xbd833e20fff1ffff

def z412 : W := mkw 0x042833eac2d39798 0xac10a0cfab0b4e5e 0xfc38ffffc3c3fff7 0xf7f0e3ffff0f0fff

def z413 : W := mkw 0x8ac188172c147145 0x022b06205cb051c5 0xefcf883ffc7cf3ff 0xbfbf3e20fff1f3cf

def z414 : W := mkw 0x1fffffbd6c02e83f 0x307ffffef5b00ba0 0xffffffffcc00c004 0xffffffffff300300

def z415 : W := mkw 0x0ac0dc437db3ff21 0x342b03710df6cffc 0xffc0fe01ffb3ff3f 0x6fff03f807fecffc

def z416 : W := mkw 0x0ac0dc416c83ea21 0x302b037105b20fa8 0xfff0ffc1ff83ff3f 0xffffc3ff07fe0ffc

def z417 : W := mkw 0x000002c800810608 0x0400000b20020418 0x000007c000030c00 0x4000001f00000c30

def z418 : W := mkw 0x8041885615b57744 0x060106215856d5dd 0x40cf883e3fffffff 0xbd033e20f8ffffff

def z419 : W := mkw 0x0000000000000000 0x0000000000000000 0x40c000000c00000d 0x0d03000000300000

def z420 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffcffe01fc7ffc3f 0x7fff3ff807f1fff0

def z421 : W := mkw 0x0b96000139280001 0x402e580004e4a000 0xc3f700003fbc001b 0x1b0fdc0000fef000

def z422 : W := mkw 0x0000104040838200 0x2000004101020e08 0xfc30f1c1c383c337 0xf7f0c3c7070e0f0c

def z423 : W := mkw 0x1bd7ce9e1130152e 0x046f5f3a7844c054 0x03c70e0e30303c08 0x080f1c3838c0c0f0

def z424 : W := mkw 0x0040880004006000 0x0001022000100180 0x40c888300c40f3fd 0xbd032220c03103cf

def z425 : W := mkw 0x0468fd60c6c3eab0 0xb811a3f5831b0faa 0xfc38fff1c3c3fff7 0xf7f0e3ffc70f0fff

def z426 : W := mkw 0x1fffefbe0010113e 0x007fffbef8004044 0xdffffffe00303339 0xff7ffffff800c0cc

def z427 : W := mkw 0x1fffffff7db3ff3f 0x347ffffffdf6cffc 0xffffffffffb3ff3f 0xfffffffffffecffc

def z428 : W := mkw 0x1fffefbc0400603e 0x007fffbef0100180 0xdffffffe0c00f02d 0xff7ffffff83003c0

def z429 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x1fcffe3e00000000 0x0c7f3ff8f8000000

def z430 : W := mkw 0x8001001600141144 0x0200040058005045 0x0007000e003c0000 0x00001c003800f000

def z431 : W := mkw 0x0000004211b11700 0x040000010846c45c 0xc3000e0033b33f3b 0x6b0c003800ceccfc

def z432 : W := mkw 0x1469fffcc2c382be 0xa851a7fff30b0e0a 0xfc38ffffc3c3c3f7 0xf7f0e3ffff0f0f0f

def z433 : W := mkw 0x0fbe02cbbbf91709 0xc43ef80b2eefe45c 0xefff01cffffc031f 0x9fbffc073ffff00c

def z434 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc33401ce33b0031b 0x9b0cd00738cec00c

def z435 : W := mkw 0x0ffedc01ff6ae821 0xf03ffb7007fdaba0 0xfff0fe01ff83fc2f 0x6fffc3f807fe0ff0

def z436 : W := mkw 0x8469a97686d573d4 0x8a11a6a5da1b55cf 0x40ff89fe0ffcf3fd 0xbd03fe27f83ff3cf

def z437 : W := mkw 0x1ffeefa80000003a 0x007ffbbea0000000 0xdff0ffc000000000 0x6f7fc3ff00000000

def z438 : W := mkw 0x01558ade11b1170c 0x0405562b7846c45c 0xc3ff8ffe33b33f3b 0xff0ffe3ff8ceccfc

def z439 : W := mkw 0x0428212000000010 0x0010a08480000000 0xdc38f1f00040c3f5 0xf770e3c7c001030f

def z440 : W := mkw 0x0ffedecbfffbff29 0xf43ffb7b2fffeffc 0xffffffcfffffff3f 0xffffffff3ffffffc

def z441 : W := mkw 0x0ac0dc41eec3eaa1 0xb82b037107bb0faa 0xffc0fe01ffc3ffff 0x6fff03f807ff0fff

def z442 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x03ff0ffe00000000 0x980ffc3ff8000000

def z443 : W := mkw 0x00001001ff6ae801 0xf000004007fdaba0 0x20000001fffffc3f 0x0080000007fffff0

def z444 : W := mkw 0x0fbe0289bb680009 0xc03ef80a26eda000 0xefff0fcffffc001f 0xffbffc3f3ffff000

def z445 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xaf300001fffc001f 0x02bcc00007fff000

def z446 : W := mkw 0x0000316040838290 0x280000c581020e0a 0x100071c000030000 0x404001c700000c00

def z447 : W := mkw 0x0000000000000000 0x0000000000000000 0xc000000000030023 0x6300000000000c00

def z448 : W := mkw 0x042a000082480000 0xc010a80002092000 0x000b0000004c0000 0x00002c0000013000

def z449 : W := mkw 0x9bd7ce9e0414716e 0x026f5f3a781051c5 0x43cf8e3e0c7cf3fd 0xbd0f3e38f831f3cf

def z450 : W := mkw 0x01558a9c0000000c 0x0005562a70000000 0xc3ff8ffe00000000 0xff0ffe3ff8000000

def z451 : W := mkw 0x0ea87561eac38ab1 0xb83aa1d587ab0e2a 0xbf3077c1f3830c02 0x42fcc1df07ce0c30

def z452 : W := mkw 0x00000001bb680001 0xc000000006eda000 0x20000001f3800002 0x0080000007ce0000

def z453 : W := mkw 0x1fbe67a80000003a 0x007ef99ea0000000 0xdfff77c000000000 0x5f7ffddf00000000

def z454 : W := mkw 0x00003160c2c38290 0xa80000c5830b0e0a 0x3000f1f1c3c3c3f7 0xe0c003c7c70f0f0f

def z455 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0x3cc0fe01cc03fc24 0x64f303f807300ff0

def z456 : W := mkw 0x0000000011200000 0x0000000000448000 0x0000000033b0001b 0x0000000000cec000

def z457 : W := mkw 0x0ee8ed2000000030 0x003ba3b480000000 0xdff8fff000000000 0xff7fe3ffc0000000

def z458 : W := mkw 0x01548aca15b17708 0x0405522b2856c5dc 0xc3f48fce3fb3ff3f 0xff0fd23f38fecffc

def z459 : W := mkw 0x1fffeffe11b1173e 0x047fffbff846c45c 0xdffffffe03b00310 0xff7ffffff80ec00c

def z460 : W := mkw 0x0000000000000000 0x0000000000000000 0x4004000000300019 0x190010000000c000

def z461 : W := mkw 0x1bd7de9d6c02e82f 0x306f5f7a75b00ba0 0xffc7fe0ffc03fc2f 0x6fff1ff83ff00ff0

def z462 : W := mkw 0x0114028800000008 0x0004500a20000000 0x03040e0e00000000 0x080c103838000000

def z463 : W := mkw 0x00001000c2428080 0xa800004003090a02 0x20000001c040c0c4 0x0080000007010303

def z464 : W := mkw 0x01140001bb680001 0xc004500006eda000 0xe3340001fffc001f 0x1b8cd00007fff000

def z465 : W := mkw 0x053c33e8d3e38698 0xac14f0cfa34f8e1a 0xff38f7f1f3c3cff7 0xf7fce3dfc7cf0f3f

def z466 : W := mkw 0x1fbe67ea11b1173a 0x047ef99fa846c45c 0xdf347fce33b33f3b 0xfb7cd1ff38ceccfc

def z467 : W := mkw 0x053c23ea93f11798 0x8c14f08faa4fc45e 0xc33c0ffe33f33ffb 0xfb0cf03ff8cfccff

def z468 : W := mkw 0x8041881604147144 0x02010620581051c5 0x4008883e0040f3f5 0xb5002220f80103cf

def z469 : W := mkw 0x1eebed3400000036 0x007bafb4d0000000 0xdcfbf1f000000000 0xf773efc7c0000000

def z470 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0x3c08f1f1c043c3e4 0xe4f023c7c7010f0f

def z471 : W := mkw 0x04283162c2d39390 0xa810a0c58b0b4e4e 0xfc3cf9ffc3f3f3ff 0xfff0f3e7ff0fcfcf

def z472 : W := mkw 0x153f23bc9368001e 0xc054fc8ef24da000 0x003f01fe03fc0010 0x9000fc07f80ff000

def z473 : W := mkw 0x0000000000000000 0x0000000000000000 0xc30000003000000b 0x0b0c000000c00000

def z474 : W := mkw 0x9ffffffec6d7f3fe 0xaa7ffffffb1b5fcf 0xffffffffcffff3ff 0xffffffffff3fffcf

def z475 : W := mkw 0x0000000004006000 0x0000000000100180 0x000000000c00f02d 0x00000000003003c0

def z476 : W := mkw 0x0fbe1041fbeb8281 0xe83ef84107efae0a 0xefff0001ffffc3ff 0x1fbffc0007ffff0f

def z477 : W := mkw 0x0469b974c2c38294 0xa811a6e5d30b0e0a 0xfcfff9ffc3c3c3f7 0xfff3ffe7ff0f0f0f

def z478 : W := mkw 0x0000004211b11700 0x040000010846c45c 0x4004080e33b33f3b 0xb900102038ceccfc

def z479 : W := mkw 0x1fbe67e811a1063a 0x047ef99fa0468418 0x9f3077c033830c02 0x427cc1df00ce0c30

def z480 : W := mkw 0x0ac0cc012c006821 0x102b033004b001a0 0xdfc0fe003c003c08 0x6f7f03f800f000f0

def z481 : W := mkw 0x0ac0dc036c12f921 0x302b03700db04be4 0xffc4fe0ffc33ff3f 0xffff13f83ff0cffc

def z482 : W := mkw 0x0fbe212000000010 0x003ef88480000000 0xdffff1f000000000 0xff7fffc7c0000000

def z483 : W := mkw 0x0ac0dc004402e820 0x302b037001100ba0 0xdfc0fe000003fc20 0x6f7f03f800000ff0

def z484 : W := mkw 0x0041881400000004 0x0001062050000000 0x0000883e00000000 0xa0000220f8000000

def z485 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc3871c1c3c30017 0x57f0e1c7070f0c00

def z486 : W := mkw 0x8469b974c6c7e2d4 0xaa11a6e5d31b1f8b 0xfcfbf1f1cfcfc3f7 0xf7f3efc7c73f3f0f

def z487 : W := mkw 0x0a80100168028001 0x202a004005a00a00 0xffc0f001fc03c02f 0x6fff03c007f00f00

def z488 : W := mkw 0x053e0001bb680001 0xc014f80006eda000 0x203f0001fffc001f 0x1080fc0007fff000

def z489 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3ff0fce3fff3f3f 0xff0ffc3f38fffcfc

def z490 : W := mkw 0x0a80540168028821 0x302a015005a00a20 0xff007e01f0033c2b 0x6bfc01f807c00cf0

def z491 : W := mkw 0x1fffefbc8240003e 0x807fffbef2090000 0xffffffffc3c00017 0xffffffffff0f0000

def z492 : W := mkw 0x81558ade15b5774c 0x0605562b7856d5dd 0xc3f70fce3fbf3f3b 0xfb0fdc3f38fefcfc

def z493 : W := mkw 0x100067a80000003a 0x0040019ea0000000 0x100077c000000000 0x404001df00000000

def z494 : W := mkw 0x0000004000810200 0x0000000100020408 0xc03881f003c3c3f7 0xf700e207c00f0f0f

def z495 : W := mkw 0x8fbe0003bf7c7141 0xc23ef8000efdf1c5 0xefff0001fffcf3ff 0x1fbffc0007fff3cf

def z496 : W := mkw 0x00000043bbf91701 0xc40000010eefe45c 0x20000001ffff3f3f 0x0080000007fffcfc

def z497 : W := mkw 0x00001040c2c38280 0xa8000041030b0e0a 0x20000001c3830002 0x00800000070e0c00

def z498 : W := mkw 0x153f23fe11b1171e 0x0454fc8ff846c45c 0xc33f0ffe33b33f3b 0xfb0cfc3ff8ceccfc

def z499 : W := mkw 0x8469b936c656f1d4 0xaa11a6e4db195bc7 0x7ccff83fcc7cf3fd 0xbdf33fe0ff31f3cf

def z500 : W := mkw 0x0a80000128000001 0x002a000004a00000 0x03c000003c000008 0x080f000000f00000

def z501 : W := mkw 0x1bd7efbc0000003e 0x006f5fbef0000000 0x13c7fffe00000000 0xe84f1ffff8000000

def z502 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3340fce03b00310 0xfb0cd03f380ec00c

def z503 : W := mkw 0x0a8010016c02e801 0x302a004005b00ba0 0xefc00001fc03fc2f 0x0fbf000007f00ff0

def z504 : W := mkw 0x0fbe000000000000 0x003ef80000000000 0xcfff00000c7c001d 0x1f3ffc000031f000

def z505 : W := mkw 0x8bd5dedf7db7ff6d 0x362f577b7df6dffd 0xffffffffffffffff 0xffffffffffffffff

def z506 : W := mkw 0x153f23bc0000001e 0x0054fc8ef0000000 0xc33f0ffe00000000 0xfb0cfc3ff8000000

def z507 : W := mkw 0x8fff8adfbffd774d 0xc63ffe2b7efff5dd 0xefff8fffffffffff 0xffbffe3fffffffff

def z508 : W := mkw 0x011433ea51b39798 0x2c0450cfa946ce5e 0xd334fffe33b3fffb 0xfb4cd3fff8cecfff

def z509 : W := mkw 0x000010004402e800 0x3000004001100ba0 0x000000000003fc20 0x0000000000000ff0

def z510 : W := mkw 0x0ea87561eac38ab1 0xb83aa1d587ab0e2a 0xff38f7f1f3c3cff7 0xf7fce3dfc7cf0f3f

def z511 : W := mkw 0x0041881400000004 0x0001062050000000 0x00cb803000000000 0x04032e00c0000000

def z512 : W := mkw 0x0114028a11301508 0x0404500a2844c054 0x43040e0e30303f39 0xb90c103838c0c0fc

def z513 : W := mkw 0x0040880004006000 0x0001022000100180 0x000088000000f020 0x20000220000003c0

def z514 : W := mkw 0x1fffefbc9368003e 0xc07fffbef24da000 0xdffffffe03fc0010 0xff7ffffff80ff000

def z515 : W := mkw 0x1041ed3400000036 0x004107b4d0000000 0x1000f03000000000 0x004003c0c0000000

def z516 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc0fe01cc00c004 0x6fff03f807300300

def z517 : W := mkw 0x04283120c2428090 0xa810a0c483090a02 0x7c08f031c040c3f5 0xb5f023c0c701030f

def z518 : W := mkw 0x80418ade0495774c 0x0601062b781255dd 0x40cf8ffe0c7ffffd 0xfd033e3ff831ffff

def z519 : W := mkw 0x1041ce9c0000002e 0x0041073a70000000 0x00000e0e00000000 0x0000003838000000

def z520 : W := mkw 0x8469a93604147154 0x0211a6a4d81051c5 0xdcfff9fe0c7cf3fd 0xff73ffe7f831f3cf

def z521 : W := mkw 0x0fbe000128000001 0x003ef80004a00000 0xefff0001fc00000f 0x1fbffc0007f00000

def z522 : W := mkw 0x053e000093680000 0xc014f800024da000 0xc33f000033fc001b 0x1b0cfc0000cff000

def z523 : W := mkw 0x8041881404046044 0x0201062050101181 0x40cf883e0c4cc0c4 0xbd033e20f8313303

def z524 : W := mkw 0x0fbe3161fbeb8291 0xe83ef8c587efae0a 0xffff71c1ffff001f 0x5ffffdc707fffc00

def z525 : W := mkw 0x9fffefbe0014117e 0x027fffbef8005045 0xdffffffe007c03d0 0xff7ffffff801f00f

def z526 : W := mkw 0x053c3160d3e38290 0xa814f0c5834f8e0a 0xff3cf1f1f3f3c3ff 0xfffcf3c7c7cfcf0f

def z527 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xef340001f3b0001b 0x1bbcd00007cec000

def z528 : W := mkw 0x0000004200911300 0x000000010802444c 0xc03409ce03b3333b 0xfb00d027380ecccc

def z529 : W := mkw 0x0000028a00101508 0x0400000a28004054 0x00000e0e00003c00 0x00000038380000f0

def z530 : W := mkw 0x053c33e8c2c38298 0xa814f0cfa30b0e0a 0xff3cffffc3c3c3f7 0xfffcf3ffff0f0f0f

def z531 : W := mkw 0x1ffeffa96c02e83b 0x307ffbfea5b00ba0 0xfff0ffc1fc03fc2f 0x6fffc3ff07f00ff0

def z532 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xfcc0f001cc03c027 0x67f303c007300f00

def z533 : W := mkw 0x0114028a11301508 0x0404500a2844c054 0x0004000e00300000 0x000010003800c000

def z534 : W := mkw 0x0fbe33ebfbfb9799 0xec3ef8cfafefee5e 0xffffffffffffffff 0xffffffffffffffff

def z535 : W := mkw 0x0b96000139280001 0x402e580004e4a000 0xefc70001fc3c000f 0x0fbf1c0007f0f000

def z536 : W := mkw 0x1fbe77e8c2c382ba 0xa87ef9dfa30b0e0a 0xbf3077c1c3830002 0x42fcc1df070e0c00

def z537 : W := mkw 0x1bd7cede11b1172e 0x046f5f3b7846c45c 0xc3f70fce33b33f3b 0xfb0fdc3f38ceccfc

def z538 : W := mkw 0x0040dc016c02e821 0x3001037005b00ba0 0x3000fe01fc03fc2f 0x60c003f807f00ff0

def z539 : W := mkw 0x0ac0cc012c006821 0x102b033004b001a0 0x00c000000c000000 0x0003000000300000

def z540 : W := mkw 0x000010016c02e801 0x3000004005b00ba0 0x20000001cc00c004 0x0080000007300300

def z541 : W := mkw 0x0000000000000000 0x0000000000000000 0xc3000e0000000000 0x6b0c003800000000

def z542 : W := mkw 0x1fbe67a80000003a 0x007ef99ea0000000 0xdf38f7f000000000 0xf77ce3dfc0000000

def z543 : W := mkw 0x8041881604147144 0x02010620581051c5 0x40c7080e0c3c3339 0xb9031c203830f0cc

def z544 : W := mkw 0x0eaa0001aa480001 0xc03aa80006a92000 0xefcb0001fc4c000f 0x0fbf2c0007f13000

def z545 : W := mkw 0x8000000204147140 0x02000000081051c5 0x400880300c7cf3fd 0xb5002200c031f3cf

def z546 : W := mkw 0x8001001604147144 0x02000400581051c5 0x000f003e0c7cf3fd 0x90003c00f831f3cf

def z547 : W := mkw 0x0428216082c10290 0x8810a085820b040a 0x403881f003c0c3f5 0xb500e207c00f030f

def z548 : W := mkw 0x0000100040028000 0x2000004001000a00 0x3c00f001c000c004 0x04f003c007000300

def z549 : W := mkw 0x1fffffbcc24280be 0xa87ffffef3090a02 0xffffffffc040c0c4 0xffffffffff010303

def z550 : W := mkw 0x0114028a00101108 0x0004500a28004044 0xc3340fce00303339 0xfb0cd03f3800c0cc

def z551 : W := mkw 0x1117029c0000000e 0x00445c0a70000000 0x0007000e00000000 0x00001c0038000000

def z552 : W := mkw 0x0a80540168028821 0x302a015005a00a20 0xff00f601f003cc27 0x67fc03d807c00f30

def z553 : W := mkw 0x1fffffbc4002803e 0x207ffffef1000a00 0xffffffffc003c027 0xffffffffff000f00

def z554 : W := mkw 0x053e000093680000 0xc014f800024da000 0x40ff00000ffc001d 0x1d03fc00003ff000

def z555 : W := mkw 0x00000001bb680001 0xc000000006eda000 0x60cf0001fffc001f 0x1d833c0007fff000

def z556 : W := mkw 0x8041881604147144 0x02010620581051c5 0x00cf883e0c7cf0cc 0x0c033e20f831f3c3

def z557 : W := mkw 0x0bd4dec97da3ee29 0x342f537b25f68fb8 0xfff0ffc1ff83fc2f 0x6fffc3ff07fe0ff0

def z558 : W := mkw 0x0eaa3161eacb8291 0xe83aa8c587ab2e0a 0xfcfbf1f1cfcfc3f7 0xf7f3efc7c73f3f0f

def z559 : W := mkw 0x0a80440128000821 0x102a011004a00020 0x0300060030000c00 0x000c001800c00030

def z560 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000040c3f5 0x000000000001030f

def z561 : W := mkw 0x8ac1dc176c16f965 0x322b07705db05be5 0xffc7fe0ffc3ffc2f 0x6fff1ff83ff0fff0

def z562 : W := mkw 0x011402c811a10608 0x0404500b20468418 0xc3340fce33830c02 0xfb0cd03f38ce0c30

def z563 : W := mkw 0x81558ade15b5774c 0x0605562b7856d5dd 0xc3348ffe33b3fffb 0xfb0cd23ff8cecfff

def z564 : W := mkw 0x9eebed3404046076 0x027bafb4d0101181 0x1ccbf0300c4cc0c4 0x04732fc0c0313303

def z565 : W := mkw 0x04283162d3f39790 0xac10a0c58b4fce5e 0xfc38f1f1f3f3ffff 0xf7f0e3c7c7cfcfff

def z566 : W := mkw 0x0428212000000010 0x0010a08480000000 0x1c08f03000000000 0x047023c0c0000000

def z567 : W := mkw 0x0fbe1001ff6ae801 0xf03ef84007fdaba0 0xefff0001fffffc3f 0x1fbffc0007fffff0

def z568 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xbc3871f1c3c303d2 0xd2f0e1c7c70f0c0f

def z569 : W := mkw 0x0000000200101100 0x0000000008004044 0x40cf080e0c7c333d 0xbd033c203831f0cc

def z570 : W := mkw 0x000002ca00911708 0x0400000b2802445c 0x000001ce00000300 0x800000073800000c

def z571 : W := mkw 0x004098016c02e801 0x3001026005b00ba0 0x60c08801fc03fc2f 0x2d83022007f00ff0

def z572 : W := mkw 0x0eeadc01ee4ae821 0xf03bab7007b92ba0 0xffcbfe01fc4ffc2f 0x6fff2ff807f13ff0

def z573 : W := mkw 0x0b9402cb39b11709 0x042e500b2ce6c45c 0xeff40fcfffb33f3f 0xffbfd03f3ffeccfc

def z574 : W := mkw 0x8155881615347144 0x020556205854d1c5 0xc3ff883e3ffcf3ff 0xbf0ffe20f8fff3cf

def z575 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xbfc0f601fc03cc06 0x46ff03d807f00f30

def z576 : W := mkw 0x0000000000000000 0x0000000000000000 0x4004080e00000000 0xb900102038000000

def z577 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x03040fce30333f28 0xe80c103f38c0ccfc

def z578 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0x3cc0f001fc03fc2f 0x04f303c007f00ff0

def z579 : W := mkw 0x053e02ca93f91708 0xc414f80b2a4fe45c 0xc33f0fce33ff3f3b 0xfb0cfc3f38cffcfc

def z580 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc30f1c1c383c027 0x67f0c3c7070e0f00

def z581 : W := mkw 0x0428316040838290 0x2810a0c581020e0a 0xdc38f1f00003c3e0 0xf770e3c7c0000f0f

def z582 : W := mkw 0x0428216082c10290 0x8810a085820b040a 0xc03801f003c303f3 0xf300e007c00f0c0f

def z583 : W := mkw 0x0040dc004402e820 0x3001037001100ba0 0x1000f0000000c000 0x004003c000000300

def z584 : W := mkw 0x9fffefbc0404607e 0x027fffbef0101181 0xdffffffe0c4cc0c4 0xff7ffffff8313303

def z585 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0x1038f1f003c3c3f0 0xf040e3c7c00f0f0f

def z586 : W := mkw 0x1bd7ce9d2c00682f 0x106f5f3a74b001a0 0x03c70e0e3c003c08 0x080f1c3838f000f0

def z587 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xeff00001ff80000f 0x0fbfc00007fe0000

def z588 : W := mkw 0x0fbe000082400000 0x803ef80002090000 0xefff0001c3c00017 0x1fbffc00070f0000

def z589 : W := mkw 0x053e000000000000 0x0014f80000000000 0x003f000000000000 0x1000fc0000000000

def z590 : W := mkw 0x0000004000810200 0x0000000100020408 0x0000000003830333 0x00000000000e0c0c

def z591 : W := mkw 0x8fff881604147144 0x023ffe20581051c5 0xcfff883e0c7cf3fd 0xbf3ffe20f831f3cf

def z592 : W := mkw 0x0000000000000000 0x0000000000000000 0xdc00f00000000000 0x677003c000000000

def z593 : W := mkw 0x8fffdc17ff7ef965 0xf23fff705ffdfbe5 0xfffffe3fffffffff 0xfffffff8ffffffff

def z594 : W := mkw 0x0041881404006004 0x0001062050100180 0x40cf883e0c00f02d 0xbd033e20f83003c0

def z595 : W := mkw 0x00000001aa480001 0xc000000006a92000 0x20000001cc4c0004 0x0080000007313000

def z596 : W := mkw 0x1eaa652000000032 0x007aa99480000000 0x1c00700000000000 0x007001c000000000

def z597 : W := mkw 0x8000000004046040 0x0200000000101181 0x000000000c4cc0c4 0x0000000000313303

def z598 : W := mkw 0x1fffefbd2800003f 0x007fffbef4a00000 0xfffffffffc00000f 0xfffffffffff00000

def z599 : W := mkw 0x0000000000000000 0x0000000000000000 0x40cf000000000000 0x1d033c0000000000

def z600 : W := mkw 0x0000100040028000 0x2000004001000a00 0x1000f0000003c020 0x604003c000000f00

def z601 : W := mkw 0x0ea83161eac38291 0xa83aa0c587ab0e0a 0xfff8f1f1ffc3c3ff 0xffffe3c7c7ff0f0f

def z602 : W := mkw 0x8041dc164416f964 0x3201077059105be5 0x50cffe3e0c7ffffd 0xfd433ff8f831ffff

def z603 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000c7c001d 0x000000000031f000

def z604 : W := mkw 0x0b94000139200001 0x002e500004e48000 0xeff40001ffb0001f 0x1fbfd00007fec000

def z605 : W := mkw 0x153f23fe11b1171e 0x0454fc8ff846c45c 0x003f01fe03b00310 0x9000fc07f80ec00c

def z606 : W := mkw 0x8ac1cc172c147965 0x122b07305cb051e5 0x43cf8e3e3c7cfffd 0xbd0f3e38f8f1f3ff

def z607 : W := mkw 0x9fffefbe0414717e 0x027fffbef81051c5 0xdffffffe0c3c3008 0xff7ffffff830f0c0

def z608 : W := mkw 0x8ac1cc1604147164 0x022b0730581051c5 0xdfcffe3e0c7cf3fd 0xff7f3ff8f831f3cf

def z609 : W := mkw 0x0114028800000008 0x0004500a20000000 0xc3340fce30033c2b 0xfb0cd03f38c00cf0

def z610 : W := mkw 0x0114000011200000 0x0004500000448000 0xc3ff00003ffc001f 0x1f0ffc0000fff000

def z611 : W := mkw 0x0428212000000010 0x0010a08480000000 0x9c3071c000000000 0x4270c1c700000000

def z612 : W := mkw 0x8469b934c646e0d4 0xaa11a6e4d3191b83 0x3ccbf031cc4cc0c4 0x04f32fc0c7313303

def z613 : W := mkw 0x153e23a80000001a 0x0054f88ea0000000 0x003001c000000000 0x0000c00700000000

def z614 : W := mkw 0x0000000000000000 0x0000000000000000 0x000880300040c0c4 0x04002200c0010303

def z615 : W := mkw 0x1eebed3400000036 0x007bafb4d0000000 0xdfcbfe3000000000 0x6f7f2ff8c0000000

def z616 : W := mkw 0x0ffecc0000000020 0x003ffb3000000000 0xdffffe0000000000 0x7f7ffff800000000

def z617 : W := mkw 0x0bd4de8b7d32fd29 0x342f537a2df4cbf4 0xffc4fe0ffc33fc2f 0x6fff13f83ff0cff0

def z618 : W := mkw 0x0ac0cc0000000020 0x002b033000000000 0xdfc0fe0030033c2b 0x6f7f03f800c00cf0

def z619 : W := mkw 0x8000004215b57740 0x060000010856d5dd 0x000000003fffffff 0x0000000000ffffff

def z620 : W := mkw 0x0000000000000000 0x0000000000000000 0x00080030004003d0 0x90002000c001000f

def z621 : W := mkw 0x0ffecc01bf686821 0xd03ffb3006fda1a0 0xefff0e01fffc3c1f 0x1fbffc3807fff0f0

def z622 : W := mkw 0x0bd4de896c02e829 0x302f537a25b00ba0 0xfff4ffcffc03fc2f 0xffffd3ff3ff00ff0

def z623 : W := mkw 0x0000000000000000 0x0000000000000000 0xc030000003800013 0x1300c000000e0000

def z624 : W := mkw 0x0fbe5401fb6a8821 0xf03ef95007edaa20 0xffff7601ffff0c1f 0x5ffffdd807fffc30

def z625 : W := mkw 0x8041881604147144 0x02010620581051c5 0x40cf883e0000f3e0 0xbd033e20f80003cf

def z626 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x833007c033b33f3b 0x420cc01f00ceccfc

def z627 : W := mkw 0x8041881404046044 0x0201062050101181 0x40cb88300c4cf0ed 0x2d032e20c03133c3

def z628 : W := mkw 0x9fffefbe0414717e 0x027fffbef81051c5 0xdffffffe0000f3e0 0xff7ffffff80003cf

def z629 : W := mkw 0x04283120c2428090 0xa810a0c483090a02 0xfc38f1f1c040c0c4 0xf7f0e3c7c7010303

def z630 : W := mkw 0x0040880004006000 0x0001022000100180 0x00c008000c003008 0x08030020003000c0

def z631 : W := mkw 0x1fbf23bc0000001e 0x007efc8ef0000000 0xcfff01fe00000000 0x9f3ffc07f8000000

def z632 : W := mkw 0x0fbe3161fbeb8291 0xe83ef8c587efae0a 0xbf3071c1f3830002 0x42fcc1c707ce0c00

def z633 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xef380001f3c00017 0x17bce00007cf0000

def z634 : W := mkw 0x0114000011200000 0x0004500000448000 0xc3340e0033b33c3b 0x7b0cd03800ceccf0

def z635 : W := mkw 0x0428312040028010 0x2010a0c481000a00 0xfc38f1f1c003c027 0xf7f0e3c7c7000f00

def z636 : W := mkw 0x0040880204107100 0x00010220081041c4 0x40c4880e0c30f33d 0xbd0312203830c3cc

def z637 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc0f001fc00c00f 0x0fff03c007f00300

def z638 : W := mkw 0x0fbe0043bbf91701 0xc43ef8010eefe45c 0xefff0001ffff3f3f 0x1fbffc0007fffcfc

def z639 : W := mkw 0x8ee9fd77eed7fbf5 0xba3ba7f5dfbb5fef 0xffffffffffffffff 0xffffffffffffffff

def z640 : W := mkw 0x84283162c6d7f3d0 0xaa10a0c58b1b5fcf 0xfc38f1f1cffff3ff 0xf7f0e3c7c73fffcf

def z641 : W := mkw 0x811502de11b5174c 0x0604540b7846d45d 0x003f01fe03fc03d0 0x9000fc07f80ff00f

def z642 : W := mkw 0x0000000200101100 0x0000000008004044 0x0004080e00303008 0x080010203800c0c0

def z643 : W := mkw 0x0bd4dc017d22e821 0x302f537005f48ba0 0xfff4fe01ffb3fc3f 0x7fffd3f807fecff0

def z644 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xaf3f0001f3fc0012 0x12bcfc0007cff000

def z645 : W := mkw 0x8ac1cc172c147965 0x122b07305cb051e5 0x03c70e0e3c3c3c08 0x080f1c3838f0f0f0

def z646 : W := mkw 0x1fffeffc11a1063e 0x047fffbff0468418 0xdffffffe33830c02 0xff7ffffff8ce0c30

def z647 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0x13c0fe003c03fc28 0x684f03f800f00ff0

def z648 : W := mkw 0x0ac088012c006001 0x002b022004b00180 0xefc08801fc00f02f 0x2fbf022007f003c0

def z649 : W := mkw 0x0000100040028000 0x2000004001000a00 0xfc08f031c043c3f7 0xf7f023c0c7010f0f

def z650 : W := mkw 0x8041881404046044 0x0201062050101181 0x40cb80300c4cc3f5 0xb5032e00c031330f

def z651 : W := mkw 0x0ee8dc01ee42e821 0xb03ba37007b90ba0 0xfff8fe01ffc3fc3f 0x7fffe3f807ff0ff0

def z652 : W := mkw 0x0ac0cc012c006821 0x102b033004b001a0 0xefc00e01fc003c0f 0x0fbf003807f000f0

def z653 : W := mkw 0x0a80540168028821 0x302a015005a00a20 0xffc07601fc030c0f 0x4fff01d807f00c30

def z654 : W := mkw 0x0040880004006000 0x0001022000100180 0xc3c08e003c03fc2f 0x6f0f023800f00ff0

def z655 : W := mkw 0x0b96000139280001 0x402e580004e4a000 0x43cf00003c7c001d 0x1d0f3c0000f1f000

def z656 : W := mkw 0x0000004011a10600 0x0400000100468418 0x0000000033830c02 0x0000000000ce0c30

def z657 : W := mkw 0x0040dc004402e820 0x3001037001100ba0 0x50c0fe000c03fc2d 0x6d4303f800300ff0

def z658 : W := mkw 0x1fffed35bb680037 0xc07fffb4d6eda000 0xfffff031fffc001f 0x1fffffc0c7fff000

def z659 : W := mkw 0x0000000000000000 0x0000000000000000 0x4008000000400015 0x1500200000010000

def z660 : W := mkw 0x004098004402e000 0x2001026001100b80 0xfcc0f801cc03f02f 0x6ff303e007300fc0

def z661 : W := mkw 0x1eebfd356c02e837 0x307baff4d5b00ba0 0x3ccbf031cc00c004 0x04f32fc0c7300300

def z662 : W := mkw 0x0a80000128000001 0x002a000004a00000 0xefc00e01fc033c2f 0x6fbf003807f00cf0

def z663 : W := mkw 0x0000004082c10280 0x88000001020b040a 0x0000000003c003d0 0x00000000000f000f

def z664 : W := mkw 0x1fffce9dbb68002f 0xc07fff3a76eda000 0xefff0e0ffffc001f 0x1fbffc383ffff000

def z665 : W := mkw 0x8469881686547144 0x8211a6205a1951c5 0xecff883fcffcf3ff 0xbfb3fe20ff3ff3cf

def z666 : W := mkw 0x8fff8817bf7c7145 0xc23ffe205efdf1c5 0xefff080ffffc301f 0x1fbffc203ffff0c0

def z667 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x003401ce33b33f3b 0x9000d00738ceccfc

def z668 : W := mkw 0x157fabbc0000001e 0x0055feaef0000000 0x40ff89fe00000000 0xbd03fe27f8000000

def z669 : W := mkw 0x81558a9e0414714c 0x0205562a781051c5 0xc3ff8ffe0c7cf3fd 0xff0ffe3ff831f3cf

def z670 : W := mkw 0x0000000200101100 0x0000000008004044 0xc3040e0e30333f3b 0xfb0c103838c0ccfc

def z671 : W := mkw 0x1ac3cc1400000026 0x006b0f3050000000 0x00c3000000000000 0x00030c0000000000

def z672 : W := mkw 0x1041ffbc4402e83e 0x304107fef1100ba0 0x1000fffe0003fc20 0xe04003fff8000ff0

def z673 : W := mkw 0x0000004000810200 0x0000000100020408 0xc3300fc033833f3b 0xfb0cc03f00ce0cfc

def z674 : W := mkw 0x0ac0dc01ff6ae821 0xf02b037007fdaba0 0xffc0fe01fffffc3f 0x6fff03f807fffff0

def z675 : W := mkw 0x8041881604147144 0x02010620581051c5 0x40c0883e0c00f3ed 0xad030220f83003cf

def z676 : W := mkw 0x811502de11b5174c 0x0604540b7846d45d 0xc33f0ffe33ff3ffb 0xfb0cfc3ff8cffcff

def z677 : W := mkw 0x9041efbe0414717e 0x024107bef81051c5 0x1000fffe0000f3e0 0xe04003fff80003cf

def z678 : W := mkw 0x0114004011a10200 0x0004500100468408 0xc33401c033b3033b 0xfb0cd00700cecc0c

def z679 : W := mkw 0x04283120c2428090 0xa810a0c483090a02 0x3c007001c0000000 0x00f001c007000000

def z680 : W := mkw 0x0041881400000004 0x0001062050000000 0x40cf883e0040c3f5 0xbd033e20f801030f

def z681 : W := mkw 0x1ffffffdeec3eabf 0xb87ffffff7bb0faa 0xffffffffffc3ffff 0xffffffffffff0fff

def z682 : W := mkw 0x011412cad3f39788 0xac04504b2b4fce5e 0xe3340fcff3f3ffff 0xfb8cd03f3fcfcfff

def z683 : W := mkw 0x0fbe0001aa480001 0xc03ef80006a92000 0xefff0001cc4c0004 0x1fbffc0007313000

def z684 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x9ffbf7f000000000 0x467fefdfc0000000

def z685 : W := mkw 0x0eaa0001aa480001 0xc03aa80006a92000 0x6ccf0001cc7c001d 0x1db33c000731f000

def z686 : W := mkw 0x0ac0fd616c83eab1 0x382b03f585b20faa 0xffc0fff1fc03ffef 0xefff03ffc7f00fff

def z687 : W := mkw 0x0ee8fd60c2c382b0 0xa83ba3f5830b0e0a 0xfff8fff1c3c3c3f7 0xffffe3ffc70f0f0f

def z688 : W := mkw 0x84293176c2d793d4 0xaa10a4c5db0b5e4f 0xfc3ff1ffc3ffc3f7 0xf7f0ffc7ff0fff0f

def z689 : W := mkw 0x011402c811a10608 0x0404500b20468418 0x003001c003800000 0x0000c007000e0000

def z690 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0x3c08f031c3c3c3f7 0x04f023c0c70f0f0f

def z691 : W := mkw 0x00001040c2c38280 0xa8000041030b0e0a 0xfc00f001c3c3c3f7 0x67f003c0070f0f0f

def z692 : W := mkw 0x8041881604147144 0x02010620581051c5 0x00cb80300c7cf3fd 0x04032e00c031f3cf

def z693 : W := mkw 0x0000216000810290 0x080000858002040a 0x000001f0000003c0 0x80000007c000000f

def z694 : W := mkw 0x0fff8815bb680005 0xc03ffe2056eda000 0xefff883ffffc001f 0xbfbffe20fffff000

def z695 : W := mkw 0x0000000000000000 0x0000000000000000 0x000080300000c3e0 0xa0000200c000030f

def z696 : W := mkw 0x8041881604147144 0x02010620581051c5 0x000f883e007cf3f0 0xb0003e20f801f3cf

def z697 : W := mkw 0x0000004000810200 0x0000000100020408 0x803001c003830002 0x4200c007000e0c00

def z698 : W := mkw 0x1eebfd356c02e837 0x307baff4d5b00ba0 0xffcbfe31fc03fc2f 0x6fff2ff8c7f00ff0

def z699 : W := mkw 0x053e000093680000 0xc014f800024da000 0x0030000003800000 0x0000c000000e0000

def z700 : W := mkw 0x0ffedc016c02e821 0x303ffb7005b00ba0 0xfffffe01fc03fc2f 0x7ffffff807f00ff0

def z701 : W := mkw 0x000033ea40939798 0x2c0000cfa9024e5e 0x1000fffe0003ffe0 0xe04003fff8000fff

def z702 : W := mkw 0x053c33ead3f39798 0xac14f0cfab4fce5e 0xfc3cf1ffc3f3c3f7 0xf7f0f3c7ff0fcf0f

def z703 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000030033c2b 0x0000000000c00cf0

def z704 : W := mkw 0x9fffffbf6c16f97f 0x327ffffefdb05be5 0xfffffffffc7fffff 0xfffffffffff1ffff

def z705 : W := mkw 0x04283161eec3ea91 0xb810a0c587bb0faa 0xfc38f1f1ffc3ffff 0xf7f0e3c7c7ff0fff

def z706 : W := mkw 0x0000000000000000 0x0000000000000000 0x00c700000c3c0008 0x08031c000030f000

def z707 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x1fcffffe00000000 0xec7f3ffff8000000

def z708 : W := mkw 0x0428212000000010 0x0010a08480000000 0xdc3cf9fe00000000 0xff70f3e7f8000000

def z709 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff0001ffbc000a 0x1fbffc0007fef000

def z710 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3ff0fce33b33f3b 0xff0ffc3f38ceccfc

def z711 : W := mkw 0x157fefbc0000003e 0x0055ffbef0000000 0x103ff1fe00000000 0x9040ffc7f8000000

def z712 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe00033c20 0xff7ffffff8000cf0

def z713 : W := mkw 0x0b9410437db3ff01 0x342e50410df6cffc 0xeff40001ffb3ff3f 0x1fbfd00007fecffc

def z714 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3340fce33833f22 0xfb0cd03f38ce0cfc

def z715 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff8031fffc001f 0xbfbffe00c7fff000

def z716 : W := mkw 0x1bd7dedcc2c382ae 0xa86f5f7b730b0e0a 0x23c70e0fc3c3c3f7 0x088f1c383f0f0f0f

def z717 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff0001fffcc3ff 0x1fbffc0007fff30f

def z718 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0x3c38f1f1c3c3c3f4 0xf4f0e3c7c70f0f0f

def z719 : W := mkw 0x8ac1dc156c06e865 0x322b077055b01ba1 0xffcffe31fc7ffcff 0x7fff3ff8c7f1fff3

def z720 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x03340fce33b33f38 0xf80cd03f38ceccfc

def z721 : W := mkw 0x0041a93400000014 0x000106a4d0000000 0x50cff9fe00000000 0xfd433fe7f8000000

def z722 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xffff7fcffffc001f 0x5ffffdff3ffff000

def z723 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xfffffffff3c00017 0xffffffffffcf0000

def z724 : W := mkw 0x8041881604147144 0x02010620581051c5 0x00cf883e0c7cf3f4 0xb4033e20f831f3cf

def z725 : W := mkw 0x8fff8817bf7c7145 0xc23ffe205efdf1c5 0xaf30883ff380f3e2 0xa2bcc220ffce03cf

def z726 : W := mkw 0x1fffefbd3928003f 0x407fffbef4e4a000 0xdffffffe3fbc001b 0xff7ffffff8fef000

def z727 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0x1000f1fe00000000 0x804003c7f8000000

def z728 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc0fe01fc43ffff 0x6fff03f807f10fff

def z729 : W := mkw 0x1ac1efbd2800003f 0x006b07bef4a00000 0xffc0fffffc00000f 0xefff03fffff00000

def z730 : W := mkw 0x1fffefbc1120003e 0x007fffbef0448000 0xdffffffe30300008 0xff7ffffff8c0c000

def z731 : W := mkw 0x1fffefbc0400603e 0x007fffbef0100180 0xdffffffe0c003008 0xff7ffffff83000c0

def z732 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xbf30fffff3800002 0xe2fcc3ffffce0000

def z733 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe30030c02 0xff7ffffff8c00c30

def z734 : W := mkw 0x1155efbc1120003e 0x004557bef0448000 0xd334fffe33b0001b 0xfb4cd3fff8cec000

def z735 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xaffb0001fffc001f 0x06bfec0007fff000

def z736 : W := mkw 0x000010016c02e801 0x3000004005b00ba0 0xff00fe01fc03fc2f 0x6ffc03f807f00ff0

def z737 : W := mkw 0x0a800001bb680001 0xc02a000006eda000 0xefcf0001fffc001f 0x1fbf3c0007fff000

def z738 : W := mkw 0x0469a93400000014 0x0011a6a4d0000000 0xdc38f9fe00000000 0xf770e3e7f8000000

def z739 : W := mkw 0x8ac1dc156c06e865 0x322b077055b01ba1 0xffc0fe31fc03fcef 0x6fff03f8c7f00ff3

def z740 : W := mkw 0x1469efbc8240003e 0x8051a7bef2090000 0xfc38ffffc3c00017 0xf7f0e3ffff0f0000

def z741 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3340fce33b33c0a 0xfb0cd03f38ceccf0

def z742 : W := mkw 0x9fbe67aa0414717a 0x027ef99ea81051c5 0x9f3077c00c7cf3fd 0x427cc1df0031f3cf

def z743 : W := mkw 0x1fffefbd2c00683f 0x107fffbef4b001a0 0xdffffffe3c033c2b 0xff7ffffff8f00cf0

def z744 : W := mkw 0x8469b976c6d7f3d4 0xaa11a6e5db1b5fcf 0xbcf779cfcfbf300a 0x4af3dde73f3efcc0

def z745 : W := mkw 0x0ac0dc0040028020 0x202b037001000a00 0xffc0fe01f003fc2f 0x6fff03f807c00ff0

def z746 : W := mkw 0x1fffefbd3920003f 0x007fffbef4e48000 0xffffffffffb0001f 0xfffffffffffec000

def z747 : W := mkw 0x0eaa02cbaad91709 0xc43aa80b2eab645c 0x2ccb0fcfcc4f3f24 0xe4b32c3f3f313cfc

def z748 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xdf34ffce33b33f3b 0xff7cd3ff38ceccfc

def z749 : W := mkw 0x1fffefbc8240003e 0x807fffbef2090000 0xdffffffe03c00010 0xff7ffffff80f0000

def z750 : W := mkw 0x0b960001bb680001 0xc02e580006eda000 0xefc70001fffc001f 0x0fbf1c0007fff000

def z751 : W := mkw 0x1fbe23a9bb68001b 0xc07ef88ea6eda000 0xefff01c1fffc001f 0x1fbffc0707fff000

def z752 : W := mkw 0x0eaa0001bb680001 0xc03aa80006eda000 0xecfb0001fffc001f 0x17b3ec0007fff000

def z753 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0xd300fffe00000000 0xeb4c03fff8000000

def z754 : W := mkw 0x800010437db7ff41 0x360000410df6dffd 0x20000001ffffffff 0x0080000007ffffff

def z755 : W := mkw 0x00419854c2c38284 0xa8010661530b0e0a 0x60cf883fc3c3c3f7 0xbd833e20ff0f0f0f

def z756 : W := mkw 0x0ac0cc0128000021 0x002b033004a00000 0xffc0fe01fc033c2f 0x6fff03f807f00cf0

def z757 : W := mkw 0x00001042c2d39380 0xa80000410b0b4e4e 0x20000001c3f3f3ff 0x00800000070fcfcf

def z758 : W := mkw 0x1fffefbc1120003e 0x007fffbef0448000 0xdffffffe33b33c3b 0xff7ffffff8ceccf0

def z759 : W := mkw 0x0114028811200008 0x0004500a20448000 0xc3340fce33b33c3b 0xfb0cd03f38ceccf0

def z760 : W := mkw 0x1fffefbd2c00603f 0x007fffbef4b00180 0xfffffffffc00f02f 0xfffffffffff003c0

def z761 : W := mkw 0x0bd4decb7db3ff29 0x342f537b2df6cffc 0x3cf4f1cfcfb0c314 0x94f3d3c73f3ec30c

def z762 : W := mkw 0x1fffefbc1120003e 0x007fffbef0448000 0xdffffffe33800002 0xff7ffffff8ce0000

def z763 : W := mkw 0x0fbe2121bb680011 0xc03ef88486eda000 0xffff71c1fffc001f 0x5ffffdc707fff000

def z764 : W := mkw 0x1fbe67a9bb68003b 0xc07ef99ea6eda000 0xfffff7f1fffc001f 0xffffffdfc7fff000

def z765 : W := mkw 0x142923bc0000001e 0x0050a48ef0000000 0xdc38f1fe00000000 0xf770e3c7f8000000

def z766 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffcffe01fc03fc2f 0x7fff3ff807f00ff0

def z767 : W := mkw 0x0b96316179ab8291 0x682e58c585e6ae0a 0x13c7f1f03c3fc3e8 0xe84f1fc7c0f0ff0f

def z768 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc3cf1f1c3f3c3ff 0xfff0f3c7c70fcf0f

def z769 : W := mkw 0x1ffeefa80000003a 0x007ffbbea0000000 0xdff4ffce00000000 0xff7fd3ff38000000

def z770 : W := mkw 0x0a80540168028821 0x302a015005a00a20 0xbf007601f0033c2b 0x42fc01d807c00cf0

def z771 : W := mkw 0x80001043fffff3c1 0xea0000410fffffcf 0x20000001fffff3ff 0x0080000007ffffcf

def z772 : W := mkw 0x1fbe67a80000003a 0x007ef99ea0000000 0x9f347fce00000000 0x4a7cd1ff38000000

def z773 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff8001fffcc03f 0x3fbffe0007fff300

def z774 : W := mkw 0x0fbe23a9bb680019 0xc03ef88ea6eda000 0xfffffffffffc001f 0xfffffffffffff000

def z775 : W := mkw 0x9fffefbc0404607e 0x027fffbef0101181 0xdffffffe0c0c0000 0xff7ffffff8303000

def z776 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xeff70001ffbc000f 0x0fbfdc0007fef000

def z777 : W := mkw 0x1fbf67bc0000003e 0x007efd9ef0000000 0xdf3ff7fe00000000 0xf77cffdff8000000

def z778 : W := mkw 0x8469881686547144 0x8211a6205a1951c5 0xec38883fc3c0f3f7 0xb7b0e220ff0f03cf

def z779 : W := mkw 0x8fbe1043fffff3c1 0xea3ef8410fffffcf 0xefff0001fffff3ff 0x1fbffc0007ffffcf

def z780 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc38fff1c3c3fff7 0xf7f0e3ffc70f0fff

def z781 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xbfc0fe01fc03fc26 0x66ff03f807f00ff0

def z782 : W := mkw 0x1fffefbc1128003e 0x407fffbef044a000 0xdffffffe003c0000 0xff7ffffff800f000

def z783 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc3ff1f1c3ffc3f7 0xf7f0ffc7c70fff0f

def z784 : W := mkw 0x1fbe77e9fbeb82bb 0xe87ef9dfa7efae0a 0xbf3077c1f3830002 0x42fcc1df07ce0c00

def z785 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc3cf9ffc3c3c3f7 0xfff0f3e7ff0f0f0f

def z786 : W := mkw 0x1041efbdbb68003f 0xc04107bef6eda000 0x3000fffffffc001f 0xe0c003fffffff000

def z787 : W := mkw 0x1fffefbd2c00683f 0x107fffbef4b001a0 0xfffffffffc003c0f 0xfffffffffff000f0

def z788 : W := mkw 0x053c23ea93f11798 0x8c14f08faa4fc45e 0x003401ce03b00310 0x9000d007380ec00c

def z789 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0x3fc0fe01fc03fc2f 0x0cff03f807f00ff0

def z790 : W := mkw 0x8041bbfe4497f7dc 0x2e0106eff9125fdf 0x1000fffe0003ffe0 0xe04003fff8000fff

def z791 : W := mkw 0x0000316040838290 0x280000c581020e0a 0xfc30f1f1c383c3f7 0xf7f0c3c7c70e0f0f

def z792 : W := mkw 0x9fffefbc0004007e 0x027fffbef0001001 0xdffffffe004c00c0 0xff7ffffff8013003

def z793 : W := mkw 0x8041cc1604147164 0x02010730581051c5 0x50cffe3e0c7cf3fd 0xfd433ff8f831f3cf

def z794 : W := mkw 0x1fffefbc8240003e 0x807fffbef2090000 0xffffffffc3c0c3f7 0xffffffffff0f030f

def z795 : W := mkw 0x9fffefbc0404607e 0x027fffbef0101181 0xdffffffe0c7cc0dd 0xff7ffffff831f303

def z796 : W := mkw 0x0fbe2121bb680011 0xc03ef88486eda000 0xfffff1f1fffcc3ff 0xffffffc7c7fff30f

def z797 : W := mkw 0x0a80540168028821 0x302a015005a00a20 0xff00fe01f003fc2f 0x6ffc03f807c00ff0

def z798 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0x1000fffe00033c20 0xe04003fff8000cf0

def z799 : W := mkw 0x1469efbc0000003e 0x0051a7bef0000000 0x1c08fffe00000000 0xe47023fff8000000

def z800 : W := mkw 0x8bd5ce9f3d347d6d 0x162f573a7cf4d1f5 0x03c70e0e3c3c3c08 0x080f1c3838f0f0f0

def z801 : W := mkw 0x1fffefbc0400603e 0x007fffbef0100180 0xdffffffe0c00c004 0xff7ffffff8300300

def z802 : W := mkw 0x1eebed7611b11736 0x047bafb5d846c45c 0x1ccbf03033b33f3b 0x04732fc0c0ceccfc

def z803 : W := mkw 0x81558adc15a5664c 0x0605562b70569599 0x83fb87f03fcfccc6 0x460fee1fc0ff3f33

def z804 : W := mkw 0x057edc00d76ae820 0xf015fb70035daba0 0x103ffe0003fffc30 0x7040fff8000ffff0

def z805 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc0fe01fc03ff3f 0xffff03f807f00ffc

def z806 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x83300fce33833c02 0x420cc03f38ce0cf0

def z807 : W := mkw 0x800010424497f3c0 0x2a00004109125fcf 0x000000000003f3e0 0x0000000000000fcf

def z808 : W := mkw 0x0ac1dc156c02e825 0x302b077055b00ba0 0xffcffe3ffc7ffc3f 0xffff3ff8fff1fff0

def z809 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff0001fffc033f 0xbfbffc0007fff00c

def z810 : W := mkw 0x153f23bc0000001e 0x0054fc8ef0000000 0x1c3ff1fe00000000 0x9470ffc7f8000000

def z811 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe0c4c0004 0xff7ffffff8313000

def z812 : W := mkw 0x1fbe67a9bb68003b 0xc07ef99ea6eda000 0xffff7fcffffc001f 0xfffffdff3ffff000

def z813 : W := mkw 0x0000104040838200 0x2000004101020e08 0xfc38f1f1c3c3c3f7 0xf7f0e3c7c70f0f0f

def z814 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3340fce33f3ffff 0xfb0cd03f38cfcfff

def z815 : W := mkw 0x0b960001bb680001 0xc02e580006eda000 0xe3f70001fffc001f 0x1b8fdc0007fff000

def z816 : W := mkw 0x0a8054016c02e821 0x302a015005b00ba0 0xbf007601fc033c0a 0x42fc01d807f00cf0

def z817 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xffffffffffbc000a 0xfffffffffffef000

def z818 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe00000331 0xff7ffffff800000c

def z819 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x1ffffffe00000000 0x9c7ffffff8000000

def z820 : W := mkw 0x011412896c02e809 0x3004504a25b00ba0 0xe3340fcffc03fc2f 0xfb8cd03f3ff00ff0

def z821 : W := mkw 0x1fffefbc0400603e 0x007fffbef0100180 0xdffffffe0000f020 0xff7ffffff80003c0

def z822 : W := mkw 0x153f33bd6c02e81f 0x3054fccef5b00ba0 0x203f01fffc03fc2f 0x9080fc07fff00ff0

def z823 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff0e01fffc3c1f 0x1fbffc3807fff0f0

def z824 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc4fe01fc33fc3f 0x7fff13f807f0cff0

def z825 : W := mkw 0x153f23fe93f1179e 0x8c54fc8ffa4fc45e 0x003f01fe03f003d0 0x9000fc07f80fc00f

def z826 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xfffff1fffffc001f 0x9fffffc7fffff000

def z827 : W := mkw 0x153f23bc0000001e 0x0054fc8ef0000000 0xdf3ffffe00000000 0xff7cfffff8000000

def z828 : W := mkw 0x00001043fff3ff81 0xbc0000410fffcffe 0x20000001fff3ffff 0x0080000007ffcfff

def z829 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe0000c025 0xff7ffffff8000300

def z830 : W := mkw 0x0000004200911300 0x000000010802444c 0xc3340fce33b33f3b 0xfb0cd03f38ceccfc

def z831 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3ff8ffe3fffffff 0xff0ffe3ff8ffffff

def z832 : W := mkw 0x1fffefbc1120003e 0x007fffbef0448000 0xdffffffe3ffc001f 0xff7ffffff8fff000

def z833 : W := mkw 0x1bd7efbc0000003e 0x006f5fbef0000000 0xd3f7fffe00000000 0xfb4fdffff8000000

def z834 : W := mkw 0x8041881604147144 0x02010620581051c5 0x40cf883e3c7fffff 0xbd033e20f8f1ffff

def z835 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe00300019 0xff7ffffff800c000

def z836 : W := mkw 0x1fffefbd3928003f 0x407fffbef4e4a000 0xdffffffe30000000 0xff7ffffff8c00000

def z837 : W := mkw 0x1fffefbd2808003f 0x407fffbef4a02000 0xdffffffe0c0c0000 0xff7ffffff8303000

def z838 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x83340fce33b33f2a 0xea0cd03f38ceccfc

def z839 : W := mkw 0x8041881604147144 0x02010620581051c5 0x00cf803e0c7cf3fd 0x94033e00f831f3cf

def z840 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x83340fce33b33f32 0xf20cd03f38ceccfc

def z841 : W := mkw 0x8041881604147144 0x02010620581051c5 0x40cf8e3e0c7ffffd 0xfd033e38f831ffff

def z842 : W := mkw 0x0ac1dc156c02e825 0x302b077055b00ba0 0xffc0fe3ffc03fc2f 0xefff03f8fff00ff0

def z843 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff0001ffff003f 0x7fbffc0007fffc00

def z844 : W := mkw 0x00001042d3f39780 0xac0000410b4fce5e 0x20000001f3b33f3b 0x0080000007ceccfc

def z845 : W := mkw 0x8041881604147144 0x02010620581051c5 0x00cf883e0c7cf3ec 0xac033e20f831f3cf

def z846 : W := mkw 0x157defbc0000003e 0x0055f7bef0000000 0xdf3cfffe00000000 0xff7cf3fff8000000

def z847 : W := mkw 0x00001042c2d39780 0xac0000410b0b4e5e 0x20000001c3c3fff7 0x00800000070f0fff

def z848 : W := mkw 0x1fffefbd3d28683f 0x507fffbef4f4a1a0 0xdffffffe3c3c3c08 0xff7ffffff8f0f0f0

def z849 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xfffffffffc7c000c 0xfffffffffff1f000

def z850 : W := mkw 0x1fffefbd2800003f 0x007fffbef4a00000 0xffffffffcc000004 0xffffffffff300000

def z851 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe03800013 0xff7ffffff80e0000

def z852 : W := mkw 0x053c33aad3729598 0xac14f0ceab4dca56 0x3f0cfe3ff070fccc 0x0cfc33f8ffc1c3f3

def z853 : W := mkw 0x1469efbc0000003e 0x0051a7bef0000000 0xdcfffffe00000000 0xff73fffff8000000

def z854 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xfffff001fffc001f 0x7fffffc007fff000

def z855 : W := mkw 0x1fbf67bc0000003e 0x007efd9ef0000000 0x9f3777ce00000000 0x427cdddf38000000

def z856 : W := mkw 0x8a81541768169965 0x322a05505da05a65 0xbf0f763ff07f0fd2 0xd2fc3dd8ffc1fc3f

def z857 : W := mkw 0x1eebfd35ee42e8b7 0xb87baff4d7b90ba2 0x3ccbf031cc40c0c4 0x04f32fc0c7310303

def z858 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdcfff1fe00000000 0xf773ffc7f8000000

def z859 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xff38fff1c3c3c3f7 0xfffce3ffc70f0f0f

def z860 : W := mkw 0x0b960001bb680001 0xc02e580006eda000 0x63cf0001fffc001f 0x1d8f3c0007fff000

def z861 : W := mkw 0x0fbe0289bb680009 0xc03ef80a26eda000 0xefff0fcfffff3c3f 0xffbffc3f3ffffcf0

def z862 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xbf00fe01fc03fc2f 0x62fc03f807f00ff0

def z863 : W := mkw 0x1bd7efbc0000003e 0x006f5fbef0000000 0x53cffffe00000000 0xfd4f3ffff8000000

def z864 : W := mkw 0x0a8054016c02e821 0x302a015005b00ba0 0xff007e01fc03fc2f 0x6bfc01f807f00ff0

def z865 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdff7ffce00000000 0x6f7fdfff38000000

def z866 : W := mkw 0x00000001bb680001 0xc000000006eda000 0x20c70001fffc001f 0x08831c0007fff000

def z867 : W := mkw 0x0428212082400010 0x8010a08482090000 0xfc38f1f1c3c0c3f7 0xf7f0e3c7c70f030f

def z868 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xeff70001ffbc001b 0x1bbfdc0007fef000

def z869 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc30f1f1c383c3f3 0xf3f0c3c7c70e0f0f

def z870 : W := mkw 0x9bd7ce9f3d3c716f 0x426f5f3a7cf4f1c5 0x03c70e0e3c3c3008 0x080f1c3838f0f0c0

def z871 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xffffffffffff3c3f 0xfffffffffffffcf0

def z872 : W := mkw 0x8041881604147144 0x02010620581051c5 0xc0ff883e0ffcf3ff 0xbf03fe20f83ff3cf

def z873 : W := mkw 0x0040ce8800000028 0x0001033a20000000 0x1000ffce00000000 0xe04003ff38000000

def z874 : W := mkw 0x9fffefbdbf6c607f 0xc27fffbef6fdb181 0xfffffffffffcc0df 0xfffffffffffff303

def z875 : W := mkw 0x1eebed3400000036 0x007bafb4d0000000 0xdcfff9fe00000000 0xff73ffe7f8000000

def z876 : W := mkw 0x1fffefbc9368003e 0xc07fffbef24da000 0xdffffffe03800000 0xff7ffffff80e0000

def z877 : W := mkw 0x8ac1dc156c06e865 0x322b077055b01ba1 0xffcbfe31fc4fffff 0xffff2ff8c7f13fff

def z878 : W := mkw 0x0000316040838290 0x280000c581020e0a 0x50cff1f00c7fc3fd 0xfd433fc7c031ff0f

def z879 : W := mkw 0x0041881400000004 0x0001062050000000 0x40cf883e0c7cc3fd 0xbd033e20f831f30f

def z880 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc38f9f1c3c3f3ff 0xfff0e3e7c70f0fcf

def z881 : W := mkw 0x8041881604147144 0x02010620581051c5 0xeccf883fcc7cf3ff 0xbfb33e20ff31f3cf

def z882 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfcfff1f1c3c3c3f7 0xfff3ffc7c70f0f0f

def z883 : W := mkw 0x0a820001bb680001 0xc02a080006eda000 0x20c30001fffc001f 0x00830c0007fff000

def z884 : W := mkw 0x8041881604147144 0x02010620581051c5 0x40cf883e0c7cc3d4 0xbd033e20f831f30f

def z885 : W := mkw 0x1fffefbd2800003f 0x007fffbef4a00000 0xfffffffff0000002 0xffffffffffc00000

def z886 : W := mkw 0x1fffefbc0400603e 0x007fffbef0100180 0xdffffffe0c7cf03d 0xff7ffffff831f3c0

def z887 : W := mkw 0x0fbe23a800000018 0x003ef88ea0000000 0xdffffffe00000000 0xff7ffffff8000000

def z888 : W := mkw 0x0b96000139280001 0x402e580004e4a000 0xeff70001ffbc001f 0x1fbfdc0007fef000

def z889 : W := mkw 0x1469efbc0000003e 0x0051a7bef0000000 0x9c30fffe00000000 0xe270c3fff8000000

def z890 : W := mkw 0x80001042c6d7f3c0 0xaa0000410b1b5fcf 0x20000001c3c3f3f7 0x00800000070f0fcf

def z891 : W := mkw 0x8041881604147144 0x02010620581051c5 0x00cf083e0c7cf3fd 0x98033c20f831f3cf

def z892 : W := mkw 0x80001042c2d793c0 0xaa0000410b0b5e4f 0x20000001c3ffc3f7 0x00800000070fff0f

def z893 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xbff77fcfffbc000a 0x4affddff3ffef000

def z894 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3300fce33833f2b 0xeb0cc03f38ce0cfc

def z895 : W := mkw 0x0fbe0289bb680009 0xc03ef80a26eda000 0xefff01cffffc001f 0x9fbffc073ffff000

def z896 : W := mkw 0x0a80100168028001 0x202a004005a00a00 0xffc0fe01fc03fc2f 0x6fff03f807f00ff0

def z897 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3340fce33b33c2b 0x6b0cd03f38ceccf0

def z898 : W := mkw 0x0a80540168028821 0x302a015005a00a20 0xbf007e01f0033c0a 0x4afc01f807c00cf0

def z899 : W := mkw 0x1bd7efbc0000003e 0x006f5fbef0000000 0x1300fffe00000000 0xe04c03fff8000000

def z900 : W := mkw 0x1fffefbd2c00683f 0x107fffbef4b001a0 0xdffffffe3c00fc2d 0xff7ffffff8f003f0

def z901 : W := mkw 0x153f23bc0000001e 0x0054fc8ef0000000 0x9c3f71fe00000000 0xd270fdc7f8000000

def z902 : W := mkw 0x1fffefbdaa48003f 0xc07fffbef6a92000 0xfffffffffc4c000f 0xfffffffffff13000

def z903 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xbc30f1f1c3c3c3f7 0xe2f0c3c7c70f0f0f

def z904 : W := mkw 0x0ac1dc156c02e825 0x302b077055b00ba0 0xffcbfe31fc03fc2f 0x6fff2ff8c7f00ff0

def z905 : W := mkw 0x0ee8ed61aec16ab1 0x983ba3b586bb05aa 0x03f80ff03fc03fd8 0x980fe03fc0ff00ff

def z906 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfcf8f1f1cfc3c3ff 0xfff3e3c7c73f0f0f

def z907 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc30f1f1c383c3e7 0xe7f0c3c7c70e0f0f

def z908 : W := mkw 0x0a8054016c02e821 0x302a015005b00ba0 0xbf007601f003fc22 0x42fc01d807c00ff0

def z909 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xfffffffff3b0001b 0xffffffffffcec000

def z910 : W := mkw 0x1ac3efbc0000003e 0x006b0fbef0000000 0x10c3fffe00000000 0xe0430ffff8000000

def z911 : W := mkw 0x0469a93482400014 0x8011a6a4d2090000 0xfcfff9ffcffc001f 0xfff3ffe7ff3ff000

def z912 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0x3fc0fe01fc03fc2c 0x6cff03f807f00ff0

def z913 : W := mkw 0x157fabbc0000001e 0x0055feaef0000000 0xdcfff9fe00000000 0xff73ffe7f8000000

def z914 : W := mkw 0x0fbe000082400000 0x803ef80002090000 0xefff0001cffc001f 0x1fbffc00073ff000

def z915 : W := mkw 0x1fffefbd3928003f 0x407fffbef4e4a000 0xdffffffe3c7c001d 0xff7ffffff8f1f000

def z916 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xafff0001fffc000e 0x0ebffc0007fff000

def z917 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x9fff7ffe00000000 0xda7ffdfff8000000

def z918 : W := mkw 0x1eebefbc0000003e 0x007bafbef0000000 0xdcfbfffe00000000 0xf773effff8000000

def z919 : W := mkw 0x8041881604147144 0x02010620581051c5 0xc3cf883e3c7cf3ff 0xbf0f3e20f8f1f3cf

def z920 : W := mkw 0x0000104251b39780 0x2c0000410946ce5e 0x0000000033b3fffb 0x0000000000cecfff

def z921 : W := mkw 0x011402c811a10608 0x0404500b20468418 0xc3340fce33833c2b 0xfb0cd03f38ce0cf0

def z922 : W := mkw 0x0ffcefa800000038 0x003ff3bea0000000 0xdffcfffe00000000 0xff7ff3fff8000000

def z923 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0x5008fffe0040c3f5 0xf54023fff801030f

def z924 : W := mkw 0x00001043fbfb9781 0xec0000410fefee5e 0x20000001ffffffff 0x0080000007ffffff

def z925 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc8fe31fc43fcef 0x6fff23f8c7f10ff3

def z926 : W := mkw 0x8041881604147144 0x02010620581051c5 0xc3cf8e3e0c7cf3fd 0xff0f3e38f831f3cf

def z927 : W := mkw 0x0fbe1043fffbff01 0xf43ef8410fffeffc 0xefff0001ffffff3f 0x1fbffc0007fffffc

def z928 : W := mkw 0x01140001bb680001 0xc004500006eda000 0xe3ff0001fffc001f 0x1f8ffc0007fff000

def z929 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc38f1f1cfffc3ff 0xf7f0e3c7c73fff0f

def z930 : W := mkw 0x1fffefbd2c00683f 0x107fffbef4b001a0 0xdffffffe0c000000 0xff7ffffff8300000

def z931 : W := mkw 0x0000104240939780 0x2c00004109024e5e 0x000000000003ffe0 0x0000000000000fff

def z932 : W := mkw 0x042a3160c2cb8290 0xe810a8c5830b2e0a 0xfc3bf1f1c3cfc3f7 0xf7f0efc7c70f3f0f

def z933 : W := mkw 0x1fffefbc8240003e 0x807fffbef2090000 0xffffffffc3800002 0xffffffffff0e0000

def z934 : W := mkw 0x0ac1dc156c02e825 0x302b077055b00ba0 0xffc7fe0ffc03fc2f 0x6fff1ff83ff00ff0

def z935 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xbc38f1f1c3c3c3e6 0xe6f0e3c7c70f0f0f

def z936 : W := mkw 0x153f23fe93f9171e 0xc454fc8ffa4fe45c 0x003f01fe03fc0310 0x9000fc07f80ff00c

def z937 : W := mkw 0x0ac0cc4211b11720 0x042b03310846c45c 0xdfc0fe0033b33f3b 0x6f7f03f800ceccfc

def z938 : W := mkw 0x00001043fffbff01 0xf40000410fffeffc 0x20000001ffffff3f 0x0080000007fffffc

def z939 : W := mkw 0x1fffefbc1120003e 0x007fffbef0448000 0xdffffffe03b00010 0xff7ffffff80ec000

def z940 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff01c1fffc001f 0xffbffc0707fff000

def z941 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0xd300fffe30033c2b 0xeb4c03fff8c00cf0

def z942 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xecff0001cffc0017 0x17b3fc00073ff000

def z943 : W := mkw 0x8041881604147144 0x02010620581051c5 0xc0ff89fe0c7cf3fd 0xff03fe27f831f3cf

def z944 : W := mkw 0x000010424493ff00 0x3400004109124ffc 0x000000000003ff20 0x0000000000000ffc

def z945 : W := mkw 0x0b960001bb680001 0xc02e580006eda000 0x23c70001ffbc000a 0x088f1c0007fef000

def z946 : W := mkw 0x0040dc004402e820 0x3001037001100ba0 0xff00fe01f003fc2f 0x6ffc03f807c00ff0

def z947 : W := mkw 0x853d23fe93f517dc 0x8e14f48ffa4fd45f 0x003f01fe03fc03d0 0x9000fc07f80ff00f

def z948 : W := mkw 0x0114028800000008 0x0004500a20000000 0xdf34ffce00000000 0xff7cd3ff38000000

def z949 : W := mkw 0x1fffefbc9368003e 0xc07fffbef24da000 0xdffffffe0ffc001d 0xff7ffffff83ff000

def z950 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc38f1f1c3c0c3d7 0x97f0e3c7c70f030f

def z951 : W := mkw 0x1fbe6521bb680033 0xc07ef99486eda000 0xffff7001fffc001f 0x1ffffdc007fff000

def z952 : W := mkw 0x8ac1dc156c06e865 0x322b077055b01ba1 0xffc3fe01fc0ffc2f 0x6fff0ff807f03ff0

def z953 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xff00fe01f003fc27 0x67fc03f807c00ff0

def z954 : W := mkw 0x8001001604147144 0x02000400581051c5 0x40cf003e0c7cf3fd 0x9d033c00f831f3cf

def z955 : W := mkw 0x1fffefbd2800003f 0x007fffbef4a00000 0xfffffffffc7c001f 0xfffffffffff1f000

def z956 : W := mkw 0x80001043eed7fbc1 0xba0000410fbb5fef 0x20000001ffffffff 0x0080000007ffffff

def z957 : W := mkw 0x004098004402e000 0x2001026001100b80 0xffc0fe01fc03fc2f 0x6fff03f807f00ff0

def z958 : W := mkw 0x0000104251b39700 0x240000410946ce5c 0x20000001f3b3ff3f 0x0080000007cecffc

def z959 : W := mkw 0x053c23a800000018 0x0014f08ea0000000 0xdc3cf1fe00000000 0xf770f3c7f8000000

def z960 : W := mkw 0x1eebefbdaa48003f 0xc07bafbef6a92000 0x3ccbffffcc4c0004 0xe4f32fffff313000

def z961 : W := mkw 0x1fffefbc0400683e 0x107fffbef01001a0 0xdffffffe00003c00 0xff7ffffff80000f0

def z962 : W := mkw 0x1fffefbc8240003e 0x807fffbef2090000 0xffffffffc0400004 0xffffffffff010000

def z963 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x9ffbfffe00000000 0xe67feffff8000000

def z964 : W := mkw 0x00000001bb680001 0xc000000006eda000 0x20cb0001fffc001f 0x04832c0007fff000

def z965 : W := mkw 0x1eebfd35ee4ae837 0xf07baff4d7b92ba0 0x3ccbf031cc4cc004 0x04f32fc0c7313300

def z966 : W := mkw 0x0ee9ed3400000034 0x003ba7b4d0000000 0xdffffffe00000000 0xff7ffffff8000000

def z967 : W := mkw 0x0000000082400000 0x8000000002090000 0x60cf0001cffc001f 0x1d833c00073ff000

def z968 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0x2fcf0001fffc001f 0x0cbf3c0007fff000

def z969 : W := mkw 0x0fffa935bb680015 0xc03ffea4d6eda000 0xfffff9fffffc001f 0xffffffe7fffff000

def z970 : W := mkw 0x011423a800000018 0x0004508ea0000000 0xd334fffe00000000 0xfb4cd3fff8000000

def z971 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc8fe31fc03fc2f 0xffff23f8c7f00ff0

def z972 : W := mkw 0x9041fffe4497f3fe 0x2a4107fff9125fcf 0x1000fffe0003f3e0 0xe04003fff8000fcf

def z973 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff080ffffc001f 0xbfbffc203ffff000

def z974 : W := mkw 0x1fffefbc9368003e 0xc07fffbef24da000 0xdffffffe33fc001b 0xff7ffffff8cff000

def z975 : W := mkw 0x9041efbc0404607e 0x024107bef0101181 0x10cbfffe0c4cc0c4 0xe4432ffff8313303

def z976 : W := mkw 0x8041881604147144 0x02010620581051c5 0x40cf803e0c7cc3dd 0x9d033e00f831f30f

def z977 : W := mkw 0x1fbe67a9bb68003b 0xc07ef99ea6eda000 0xff347fcff3b0001b 0xfbfcd1ff3fcec000

def z978 : W := mkw 0x0bd5ce9c0000002c 0x002f573a70000000 0xdffffffe00000000 0xff7ffffff8000000

def z979 : W := mkw 0x0eaa0001bb680001 0xc03aa80006eda000 0x6ccf0001fffc001f 0x1db33c0007fff000

def z980 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x13fffffe00000000 0xf84ffffff8000000

def z981 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0x3c38f1f1c3c3c3f7 0x94f0e3c7c70f0f0f

def z982 : W := mkw 0x1fbf67bc0000003e 0x007efd9ef0000000 0x1c3f71fe00000000 0x9070fdc7f8000000

def z983 : W := mkw 0x153f67bc0000003e 0x0054fd9ef0000000 0x103f77fe00000000 0xd040fddff8000000

def z984 : W := mkw 0x0ffece8800000028 0x003ffb3a20000000 0xdfffffce00000000 0xff7fffff38000000

def z985 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xbfc0f601fc03fc2f 0x46ff03d807f00ff0

def z986 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x1cfffffe00000000 0xf473fffff8000000

def z987 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3348fce33b3ff3f 0xff0cd23f38cecffc

def z988 : W := mkw 0x1fffefbc9360003e 0x807fffbef24d8000 0xfffffffff3f0001f 0xffffffffffcfc000

def z989 : W := mkw 0x0a8054016c02e821 0x302a015005b00ba0 0xffc07601fc03fc2f 0x4fff01d807f00ff0

def z990 : W := mkw 0x053c23a893600018 0x8014f08ea24d8000 0xff3cfffff3f0001f 0xfffcf3ffffcfc000

def z991 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xffffffffffcc0006 0xffffffffffff3000

def z992 : W := mkw 0x1fffefbc8240003e 0x807fffbef2090000 0xffffffffcffc001f 0xffffffffff3ff000

def z993 : W := mkw 0x1041efbc0400603e 0x004107bef0100180 0x1000fffe0000f020 0xe04003fff80003c0

def z994 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x5cfff9fe00000000 0xbd73ffe7f8000000

def z995 : W := mkw 0x1fffefbdaa48003f 0xc07fffbef6a92000 0xffffffffc0000000 0xffffffffff000000

def z996 : W := mkw 0x8041881604147144 0x02010620581051c5 0xdccff83e0c7cf3fd 0xff733fe0f831f3cf

def z997 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xafff0001fffc001a 0x1abffc0007fff000

def z998 : W := mkw 0x011402c800810208 0x0004500b20020408 0xc3340fce33833f3b 0xfb0cd03f38ce0cfc

def z999 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xbfc0fe01fc03fc2a 0x6aff03f807f00ff0

def z1000 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x83300fce33b33f3b 0xe20cc03f38ceccfc

def z1001 : W := mkw 0x0fbe0289bb680009 0xc03ef80a26eda000 0xefff07c1fffc001f 0x5fbffc1f07fff000

def z1002 : W := mkw 0x1ac1efbc0000003e 0x006b07bef0000000 0x1cc0fffe00000000 0xe47303fff8000000

def z1003 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc4fe0ffc03fc2f 0xffff13f83ff00ff0

def z1004 : W := mkw 0x0ac0ce8800000028 0x002b033a20000000 0xdfc0ffce00000000 0xef7f03ff38000000

def z1005 : W := mkw 0x9041efbc0404607e 0x024107bef0101181 0x1000fffe0000c0c0 0xe04003fff8000303

def z1006 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc33c8ffe33b33f3b 0xff0cf23ff8ceccfc

def z1007 : W := mkw 0x0041a93400000014 0x000106a4d0000000 0x1000f9fe00000000 0xe04003e7f8000000

def z1008 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0x50cffffe0c7c001d 0xfd433ffff831f000

def z1009 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0x2cff0001fffc001f 0x14b3fc0007fff000

def z1010 : W := mkw 0x1fbf67bc0000003e 0x007efd9ef0000000 0xdf3f7ffe00000000 0xfb7cfdfff8000000

def z1011 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xef340fcff3b33f3f 0xffbcd03f3fceccfc

def z1012 : W := mkw 0x1041efbc0400603e 0x004107bef0100180 0x50c0fffe0c00f02d 0xed4303fff83003c0

def z1013 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xafff0001fffc0016 0x16bffc0007fff000

def z1014 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe0000c3e0 0xff7ffffff800030f

def z1015 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffcbfe01fc4ffc2f 0x6fff2ff807f13ff0

def z1016 : W := mkw 0x8041881604147144 0x02010620581051c5 0x00cf883e0c7cf3fd 0x0c033e20f831f3cf

def z1017 : W := mkw 0x0eaa0001aa480001 0xc03aa80006a92000 0xecff0001cffc001f 0x1fb3fc00073ff000

def z1018 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff0801fffc303f 0x3fbffc2007fff0c0

def z1019 : W := mkw 0x000002ca00911708 0x0400000b2802445c 0xc3300fce33833f3b 0xfb0cc03f38ce0cfc

def z1020 : W := mkw 0x1fbe67a80000003a 0x007ef99ea0000000 0xdfff7fce00000000 0xff7ffdff38000000

def z1021 : W := mkw 0x0ea80001aa400001 0x803aa00006a90000 0xefff0001fffc001f 0x1fbffc0007fff000

def z1022 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3300fce33833f33 0xf30cc03f38ce0cfc

def z1023 : W := mkw 0x1041efbc0400683e 0x104107bef01001a0 0x1000fffe00003c00 0xe04003fff80000f0

def z1024 : W := mkw 0x1fffefbd2800083f 0x107fffbef4a00020 0xdffffffe30000c00 0xff7ffffff8c00030

def z1025 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe00400015 0xff7ffffff8010000

def z1026 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xbc38f1f1c3c3c3f2 0xf2f0e3c7c70f0f0f

def z1027 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0xd030fffe00000000 0xf340c3fff8000000

def z1028 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc38f1f1c383c3e2 0xf7f0e3c7c70e0f0f

def z1029 : W := mkw 0x8ac0dc016c06e861 0x322b037005b01ba1 0xffc0fe01fc4ffcef 0x6fff03f807f13ff3

def z1030 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0x23ff0001fffc001f 0x188ffc0007fff000

def z1031 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdf38fffe00000000 0xf77ce3fff8000000

def z1032 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x9ffff7fe00000000 0xd67fffdff8000000

def z1033 : W := mkw 0x00001042d3f39780 0xac0000410b4fce5e 0x20000001c3f3c3f7 0x00800000070fcf0f

def z1034 : W := mkw 0x1fffefbd2800003f 0x007fffbef4a00000 0xfffffffffc033c2f 0xfffffffffff00cf0

def z1035 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0x7c38f1f1c3c0c3f5 0xb5f0e3c7c70f030f

def z1036 : W := mkw 0x1fffefbc9368003e 0xc07fffbef24da000 0xffffffffc3fc0017 0xffffffffff0ff000

def z1037 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3340fce3fff3f3f 0xfb0cd03f38fffcfc

def z1038 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc07e01fc033c2b 0x6bff01f807f00cf0

def z1039 : W := mkw 0x0a80540168028821 0x302a015005a00a20 0xbf007e01f0033c22 0x62fc01f807c00cf0

def z1040 : W := mkw 0x0fbe1043fbfb9781 0xec3ef8410fefee5e 0xefff0001ffffffff 0x1fbffc0007ffffff

def z1041 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfcfbf1f1cfcfc3f7 0xf7f3efc7c73f3f0f

def z1042 : W := mkw 0x8041cc1604147964 0x12010730581051e5 0x40cf8e3e0c7cfffd 0xbd033e38f831f3ff

def z1043 : W := mkw 0x80001042d7f7f7c0 0xae0000410b5fdfdf 0x20000001ffffffff 0x0080000007ffffff

def z1044 : W := mkw 0x053c23a800000018 0x0014f08ea0000000 0xdf347fce00000000 0xfb7cd1ff38000000

def z1045 : W := mkw 0x011602ca11b91708 0x4404580b2846e45c 0xc3370fce33bf3f3b 0xfb0cdc3f38cefcfc

def z1046 : W := mkw 0x0fbe0289bb680009 0xc03ef80a26eda000 0xefff0e0ffffc001f 0x1fbffc383ffff000

def z1047 : W := mkw 0x0bd4ce8939200029 0x002f533a24e48000 0xfff4ffcfffb0001f 0xffffd3ff3ffec000

def z1048 : W := mkw 0x8041881604147144 0x02010620581051c5 0x43cf8e3e3c7cfffd 0xbd0f3e38f8f1f3ff

def z1049 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc33c0fce33f33f3f 0xff0cf03f38cfccfc

def z1050 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xaff70001fffc001f 0x0abfdc0007fff000

def z1051 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xfffffffffffcc3ff 0xfffffffffffff30f

def z1052 : W := mkw 0x1155efbc0000003e 0x004557bef0000000 0xd3fffffe00000000 0xff4ffffff8000000

def z1053 : W := mkw 0x9fffefbc0404607e 0x027fffbef0101181 0xdffffffe0c4cf0ed 0xff7ffffff83133c3

def z1054 : W := mkw 0x1fbe67a80000003a 0x007ef99ea0000000 0x9f307fce00000000 0xe27cc1ff38000000

def z1055 : W := mkw 0x053c000093600000 0x8014f000024d8000 0xefff0001fffc001f 0x1fbffc0007fff000

def z1056 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff0001ffff3c3f 0x1fbffc0007fffcf0

def z1057 : W := mkw 0x1fffefbdaa40003f 0x807fffbef6a90000 0xffffffffffc0001f 0xffffffffffff0000

def z1058 : W := mkw 0x1bd7efbc0000003e 0x006f5fbef0000000 0xdfc7fffe00000000 0xef7f1ffff8000000

def z1059 : W := mkw 0x1fbf23bc0000001e 0x007efc8ef0000000 0xdffff1fe00000000 0xff7fffc7f8000000

def z1060 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0x5008fffe00000000 0xf54023fff8000000

def z1061 : W := mkw 0x8428212204147150 0x0210a084881051c5 0xdc38f1f00c7cf3fd 0xf770e3c7c031f3cf

def z1062 : W := mkw 0x0000104255b3ff00 0x340000410956cffc 0x0000000033b3ff3b 0x0000000000cecffc

def z1063 : W := mkw 0x0b94468800000028 0x002e511a20000000 0xdf347fce00000000 0xfb7cd1ff38000000

def z1064 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x83340fce33b33f1a 0xda0cd03f38ceccfc

def z1065 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc7fe01fc3ffc2f 0x6fff1ff807f0fff0

def z1066 : W := mkw 0x0000100040028000 0x2000004001000a00 0xff007e01f0033c2b 0x6bfc01f807c00cf0

def z1067 : W := mkw 0x1bd5efbc0000003e 0x006f57bef0000000 0xdff4fffe00000000 0xff7fd3fff8000000

def z1068 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xbf007e01f0033c02 0x42fc01f807c00cf0

def z1069 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xbc38f1f1c3c3c3f7 0x46f0e3c7c70f0f0f

def z1070 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc0fe31fc03ffef 0xefff03f8c7f00fff

def z1071 : W := mkw 0x1fbf67bc0000003e 0x007efd9ef0000000 0xdfff77fe00000000 0xdf7ffddff8000000

def z1072 : W := mkw 0x1ac3dc156c02e827 0x306b0f7055b00ba0 0xffc3fe01fc03fc2f 0x6fff0ff807f00ff0

def z1073 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0x1000fffe0000c3e0 0xe04003fff800030f

def z1074 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc0fe01fc7ffc3f 0x6fff03f807f1fff0

def z1075 : W := mkw 0x8ac1dc156c06e865 0x322b077055b01ba1 0xffcffe3ffc4ffcef 0xffff3ff8fff13ff3

def z1076 : W := mkw 0x1fffefbdaa48003f 0xc07fffbef6a92000 0xffffffffcc7c001d 0xffffffffff31f000

def z1077 : W := mkw 0x1bd7efbc0000003e 0x006f5fbef0000000 0x13c77fce00000000 0x484f1dff38000000

def z1078 : W := mkw 0x057dabbc0000001c 0x0015f6aef0000000 0xdffffffe00000000 0xff7ffffff8000000

def z1079 : W := mkw 0x8001001600141144 0x0200040058005045 0x40cf803e0c7cc3fd 0xbd033e00f831f30f

def z1080 : W := mkw 0x0ac1dc156c02e825 0x302b077055b00ba0 0xffcffe3ffc43ffff 0xffff3ff8fff10fff

def z1081 : W := mkw 0x1ac1efbc0000003e 0x006b07bef0000000 0xdfcffffe00000000 0xff7f3ffff8000000

def z1082 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xfff0ffc1fc03fc2f 0xffffc3ff07f00ff0

def z1083 : W := mkw 0x0b94000139200001 0x002e500004e48000 0xefff0001fffc001f 0x1fbffc0007fff000

def z1084 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x03340fce33b33f3b 0x980cd03f38ceccfc

def z1085 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdfff7fce00000000 0x5f7ffdff38000000

def z1086 : W := mkw 0x1fffefbc8248003e 0xc07fffbef2092000 0xdffffffe004c0000 0xff7ffffff8013000

def z1087 : W := mkw 0x100067a80000003a 0x0040019ea0000000 0x10007fce00000000 0xe04001ff38000000

def z1088 : W := mkw 0x1fffefbd3928003f 0x407fffbef4e4a000 0xfffffffffc3c000f 0xfffffffffff0f000

def z1089 : W := mkw 0x1fffefbdbf68603f 0xc07fffbef6fda180 0xfffffffffffcf03f 0xfffffffffffff3c0

def z1090 : W := mkw 0x1fffefbc0400603e 0x007fffbef0100180 0xdffffffe0c40f3fd 0xff7ffffff83103cf

def z1091 : W := mkw 0x053c1042d3f39780 0xac14f0410b4fce5e 0xef3c0001f3f3ffff 0x1fbcf00007cfcfff

def z1092 : W := mkw 0x1155efbc0000003e 0x004557bef0000000 0x9330fffe00000000 0xe24cc3fff8000000

def z1093 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe0c7cc3fd 0xff7ffffff831f30f

def z1094 : W := mkw 0x0000104379b39f01 0x340000410de6ce7c 0x20000001f3b33f3b 0x0080000007ceccfc

def z1095 : W := mkw 0x0ac0dc0168028821 0x302b037005a00a20 0xffc0fe01f0033c2b 0x6fff03f807c00cf0

def z1096 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdff77fce00000000 0xfb7fddff38000000

def z1097 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xff38f7f1f3c3cff7 0xf7fce3dfc7cf0f3f

def z1098 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff0e01fffc001f 0x7fbffc3807fff000

def z1099 : W := mkw 0x9fffefbc0404607e 0x027fffbef0101181 0xdffffffe0000c0c0 0xff7ffffff8000303

def z1100 : W := mkw 0x053e0001bb680001 0xc014f80006eda000 0x60ff0001fffc001f 0x1d83fc0007fff000

def z1101 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc0fe01f003fc22 0x6fff03f807c00ff0

def z1102 : W := mkw 0x1fffefbdaa48003f 0xc07fffbef6a92000 0xffffffffcfcc0017 0xffffffffff3f3000

def z1103 : W := mkw 0x9fffefbc0404607e 0x027fffbef0101181 0xdffffffe0c4cc3f5 0xff7ffffff831330f

def z1104 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe0040c0c4 0xff7ffffff8010303

def z1105 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0x6cff0001cffc001d 0x1db3fc00073ff000

def z1106 : W := mkw 0x1fffefbc0400603e 0x007fffbef0100180 0xdffffffe3c03fc2f 0xff7ffffff8f00ff0

def z1107 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe0c3c0008 0xff7ffffff830f000

def z1108 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x9f3ffffe00000000 0xf27cfffff8000000

def z1109 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff0001cffc0014 0x1fbffc00073ff000

def z1110 : W := mkw 0x8041881604147144 0x02010620581051c5 0x00cf883e0c7cf3f8 0xb8033e20f831f3cf

def z1111 : W := mkw 0x1fbf67bc0000003e 0x007efd9ef0000000 0x9f3077fe00000000 0xc27cc1dff8000000

def z1112 : W := mkw 0x000023a800000018 0x0000008ea0000000 0x1000fffe00000000 0xe04003fff8000000

def z1113 : W := mkw 0x1fffefbc1120043e 0x047fffbef0448010 0xdffffffe30000c00 0xff7ffffff8c00030

def z1114 : W := mkw 0x157fefbc0000003e 0x0055ffbef0000000 0xd33ffffe00000000 0xfb4cfffff8000000

def z1115 : W := mkw 0x1157efbc0000003e 0x00455fbef0000000 0x1007fffe00000000 0xe0401ffff8000000

def z1116 : W := mkw 0x1fffefbdbf68683f 0xd07fffbef6fda1a0 0xfffffffffffc3c1f 0xfffffffffffff0f0

def z1117 : W := mkw 0x153f23bc0000001e 0x0054fc8ef0000000 0x103ff1fe00000000 0xf040ffc7f8000000

def z1118 : W := mkw 0x84281042c6d7f3c0 0xaa10a0410b1b5fcf 0xecff0001cffff3ff 0x1fb3fc00073fffcf

def z1119 : W := mkw 0x9fffefbdae4c607f 0xc27fffbef6b93181 0xffffffffcc4cc0c4 0xffffffffff313303

def z1120 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xffffffffcffc0014 0xffffffffff3ff000

def z1121 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc38f1f1f3c3ffff 0xf7f0e3c7c7cf0fff

def z1122 : W := mkw 0x1eebefbc0000003e 0x007bafbef0000000 0x1ccbf1fe00000000 0x84732fc7f8000000

def z1123 : W := mkw 0x1ac1efbc0000003e 0x006b07bef0000000 0x9f00fffe00000000 0xe27c03fff8000000

def z1124 : W := mkw 0x1155efbc0000003e 0x004557bef0000000 0x1034fffe00000000 0xf040d3fff8000000

def z1125 : W := mkw 0x157fefbc0000003e 0x0055ffbef0000000 0xdc3ffffe00000000 0xf770fffff8000000

def z1126 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x9f307fce00000000 0x427cc1ff38000000

def z1127 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe0c00000d 0xff7ffffff8300000

def z1128 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdff0fffe00000000 0xef7fc3fff8000000

def z1129 : W := mkw 0x0fbe33e9fbeb8699 0xec3ef8cfa7efae1a 0xbf3077c1f3830c02 0x42fcc1df07ce0c30

def z1130 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdf34fffe00000000 0xfb7cd3fff8000000

def z1131 : W := mkw 0x100123bc0000001e 0x0040048ef0000000 0x1000f1fe00000000 0xe04003c7f8000000

def z1132 : W := mkw 0x1fbe67a80000003a 0x007ef99ea0000000 0x9f3477ce00000000 0xd27cd1df38000000

def z1133 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3340fce33b33c1b 0x5b0cd03f38ceccf0

def z1134 : W := mkw 0x0429213400000014 0x0010a484d0000000 0xdc3ff1fe00000000 0xf770ffc7f8000000

def z1135 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xdffffffe3ffc0018 0xff7ffffff8fff000

def z1136 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0xdc00fffe00000000 0xe77003fff8000000

def z1137 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3348ffe33b3fffb 0xfb0cd23ff8cecfff

def z1138 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3f40fce3fb33f3f 0xff0fd03f38feccfc

def z1139 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xbfc0fe01fc03fc0e 0x4eff03f807f00ff0

def z1140 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0x10cbfffe00000000 0xe4432ffff8000000

def z1141 : W := mkw 0x0fbe2121bb680011 0xc03ef88486eda000 0xefff01f1fffc001f 0x9fbffc07c7fff000

def z1142 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff0601ffff0c1f 0x5fbffc1807fffc30

def z1143 : W := mkw 0x1eebefbc0000003e 0x007bafbef0000000 0xdfcbfffe00000000 0xef7f2ffff8000000

def z1144 : W := mkw 0x1ac1efbc0000003e 0x006b07bef0000000 0x13c0fffe00000000 0xe84f03fff8000000

def z1145 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc33f0fce33ff3f3b 0xfb0cfc3f38cffcfc

def z1146 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0x100ffffe00000000 0xf0403ffff8000000

def z1147 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc0fe01fc033c0a 0x6fff03f807f00cf0

def z1148 : W := mkw 0x157fefbc0000003e 0x0055ffbef0000000 0x50fffffe00000000 0xfd43fffff8000000

def z1149 : W := mkw 0x100167bc0000003e 0x0040059ef0000000 0x100077fe00000000 0xc04001dff8000000

def z1150 : W := mkw 0x804198564497f3c4 0x2a01066159125fcf 0x0000883e0003f3e0 0xa0000220f8000fcf

def z1151 : W := mkw 0x1ee9efbc0000003e 0x007ba7bef0000000 0xdff8fffe00000000 0xff7fe3fff8000000

def z1152 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc8fe01fc43fc3f 0x7fff23f807f10ff0

def z1153 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xbc38f1f1c3c3c3d6 0xd6f0e3c7c70f0f0f

def z1154 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe00003029 0xff7ffffff80000c0

def z1155 : W := mkw 0x0ffece89bb680029 0xc03ffb3a26eda000 0xffffffcffffc001f 0xffffffff3ffff000

def z1156 : W := mkw 0x0a80540168028821 0x302a015005a00a20 0xffc07e01fc033c2f 0x6fff01f807f00cf0

def z1157 : W := mkw 0x8041881604147144 0x02010620581051c5 0x40cf803e0c7cc3f5 0xb5033e00f831f30f

def z1158 : W := mkw 0x811402ca11b51748 0x0604500b2846d45d 0xc3340fce33ff3ffb 0xfb0cd03f38cffcff

def z1159 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0x10007fce00000000 0x404001ff38000000

def z1160 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0x50c0fffe00000000 0xed4303fff8000000

def z1161 : W := mkw 0x111467a80000003a 0x0044519ea0000000 0xd3347fce00000000 0xfb4cd1ff38000000

def z1162 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe007c0010 0xff7ffffff801f000

def z1163 : W := mkw 0x0eaa0001bb680001 0xc03aa80006eda000 0x2ccb0001cffc0014 0x04b32c00073ff000

def z1164 : W := mkw 0x1bd7ce9c0000002e 0x006f5f3a70000000 0xdff7ffce00000000 0xff7fdfff38000000

def z1165 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0x5004fffe00000000 0xf94013fff8000000

def z1166 : W := mkw 0x0ac2dc016c0ae821 0x702b0b7005b02ba0 0xffc3fe01fc0ffc2f 0x6fff0ff807f03ff0

def z1167 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe3000000b 0xff7ffffff8c00000

def z1168 : W := mkw 0x1bd7efbd3928003f 0x406f5fbef4e4a000 0x13c7fffe3c3c0008 0xe84f1ffff8f0f000

def z1169 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff8031fffcc0df 0x1fbffe00c7fff303

def z1170 : W := mkw 0x0fbe4401bb680821 0xd03ef91006eda020 0xefff0601fffc0c1f 0x1fbffc1807fff030

def z1171 : W := mkw 0x153f23bc9368001e 0xc054fc8ef24da000 0xfc3ff1ffc3fc0017 0xf7f0ffc7ff0ff000

def z1172 : W := mkw 0x053e23ea93f91798 0xcc14f88faa4fe45e 0x003f01fe03fc03d0 0x9000fc07f80ff00f

def z1173 : W := mkw 0x1eebefbc0000003e 0x007bafbef0000000 0x5ccffffe00000000 0xfd733ffff8000000

def z1174 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0x3cfff1ffcffc0014 0x94f3ffc7ff3ff000

def z1175 : W := mkw 0x157fefbc9368003e 0xc055ffbef24da000 0x103ffffe03fc0010 0xf040fffff80ff000

def z1176 : W := mkw 0x1fffefbd2800003f 0x007fffbef4a00000 0xdffffffe3c000008 0xff7ffffff8f00000

def z1177 : W := mkw 0x1fffefbc824000be 0x887fffbef2090002 0xdffffffe004000c0 0xff7ffffff8010003

def z1178 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffc07e01fc033c0f 0x4fff01f807f00cf0

def z1179 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xbfc07e01fc03fc2f 0x4aff01f807f00ff0

def z1180 : W := mkw 0x157fefbc0000003e 0x0055ffbef0000000 0x1030fffe00000000 0xe040c3fff8000000

def z1181 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe00030023 0xff7ffffff8000c00

def z1182 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffff1fe00000000 0x9f7fffc7f8000000

def z1183 : W := mkw 0x0fbe2121bb680011 0xc03ef88486eda000 0xfffff031fffc001f 0x1fffffc0c7fff000

def z1184 : W := mkw 0x053e000093680000 0xc014f800024da000 0xecff0001cffc001f 0x1fb3fc00073ff000

def z1185 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0x2fff0001fffc001c 0x1cbffc0007fff000

def z1186 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x9ffffffe00000000 0x4e7ffffff8000000

def z1187 : W := mkw 0x1fbe67a80000003a 0x007ef99ea0000000 0xdf3cfffe00000000 0xff7cf3fff8000000

def z1188 : W := mkw 0x146befbc0000003e 0x0051afbef0000000 0x100bfffe00000000 0xe0402ffff8000000

def z1189 : W := mkw 0x8041dede4497ff6c 0x3601077b79125ffd 0x1000fffe0003ffe0 0xe04003fff8000fff

def z1190 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc33c0ffe33f33ffb 0xfb0cf03ff8cfccff

def z1191 : W := mkw 0x0fbe0001bb680001 0xc03ef80006eda000 0xefff0031fffc03df 0x9fbffc00c7fff00f

def z1192 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xfc38f1f1c3c0c3d4 0xf7f0e3c7c70f030f

def z1193 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xff00fe01f003fc2b 0x6bfc03f807c00ff0

def z1194 : W := mkw 0x8041fd764497fbf4 0x3a0107f5d9125fef 0x1000fffe0003ffe0 0xe04003fff8000fff

def z1195 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xffffffffff80000f 0xfffffffffffe0000

def z1196 : W := mkw 0x1469efbc0000003e 0x0051a7bef0000000 0x1038fffe00000000 0xf040e3fff8000000

def z1197 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0x9ff7fffe00000000 0xea7fdffff8000000

def z1198 : W := mkw 0x000010436c93ff01 0x340000410db24ffc 0x20000001fc03ff2f 0x0080000007f00ffc

def z1199 : W := mkw 0x1eebefbc0000003e 0x007bafbef0000000 0x1c00fffe00000000 0xe07003fff8000000

def z1200 : W := mkw 0x800010424497f3c0 0x2a00004109125fcf 0x000000000c7ff3fd 0x000000000031ffcf

def z1201 : W := mkw 0x0a8054016c02e821 0x302a015005b00ba0 0xff00f601fc03fc2f 0x67fc03d807f00ff0

def z1202 : W := mkw 0x8041881604147144 0x02010620581051c5 0xc0cf883e0c7ff3ff 0xff033e20f831ffcf

def z1203 : W := mkw 0x04283160c2c38290 0xa810a0c5830b0e0a 0xff38f1f1f3c3c3ff 0xfffce3c7c7cf0f0f

def z1204 : W := mkw 0x0fffa93400000014 0x003ffea4d0000000 0xdffff9fe00000000 0xff7fffe7f8000000

def z1205 : W := mkw 0x1fbe4689bb68002b 0xc07ef91a26eda000 0xefff0601fffc001f 0x1fbffc1807fff000

def z1206 : W := mkw 0x0fbe2121bb680091 0xc83ef88486eda002 0xefff0031fffc00df 0x1fbffc00c7fff003

def z1207 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe30003c08 0xff7ffffff8c000f0

def z1208 : W := mkw 0x042823a800000018 0x0010a08ea0000000 0xdc38fffe00000000 0xf770e3fff8000000

def z1209 : W := mkw 0x1fbf23bdbb68001f 0xc07efc8ef6eda000 0xfffff1fffffc001f 0xffffffc7fffff000

def z1210 : W := mkw 0x1ac1efbd2c00683f 0x106b07bef4b001a0 0x13c0fffe3c003c08 0xe84f03fff8f000f0

def z1211 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0xc3f70fce3fbf3f3b 0xfb0fdc3f38fefcfc

def z1212 : W := mkw 0x8041881604147144 0x02010620581051c5 0x00cf883e0c7cf3dc 0x9c033e20f831f3cf

def z1213 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xffffffffc0000007 0xffffffffff000000

def z1214 : W := mkw 0x1fbf67bdbb68003f 0xc07efd9ef6eda000 0xbf3f77fff3fc0012 0xd2fcfddfffcff000

def z1215 : W := mkw 0x1155efbc0000003e 0x004557bef0000000 0x1304fffe00000000 0xe84c13fff8000000

def z1216 : W := mkw 0x8ee9fd35ee46e8f5 0xba3ba7f4d7b91ba3 0x3ccbf031cc4cc0c4 0x04f32fc0c7313303

def z1217 : W := mkw 0x0154ce8800000028 0x0005533a20000000 0xd334ffce00000000 0xfb4cd3ff38000000

def z1218 : W := mkw 0x0fbe4401bb680021 0xc03ef91006eda000 0xffff7601fffc001f 0x5ffffdd807fff000

def z1219 : W := mkw 0x04280001bb680001 0xc010a00006eda000 0xecff0001fffc001f 0x1fb3fc0007fff000

def z1220 : W := mkw 0x0eaa0001bb680001 0xc03aa80006eda000 0xefcb0001fffc001f 0x0fbf2c0007fff000

def z1221 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xfff0fe01ff83fc3f 0x7fffc3f807fe0ff0

def z1222 : W := mkw 0x0fbe0289bb680409 0xc43ef80a26eda010 0xefff0601fffc0c1f 0x1fbffc1807fff030

def z1223 : W := mkw 0x011402ca11b11708 0x0404500b2846c45c 0x83340fce33b33f3b 0x4a0cd03f38ceccfc

def z1224 : W := mkw 0x1041efbc0000003e 0x004107bef0000000 0x10c7fffe00000000 0xe8431ffff8000000

def z1225 : W := mkw 0x1fffefbdbb68003f 0xc07fffbef6eda000 0xfffffffff3fc0012 0xffffffffffcff000

def z1226 : W := mkw 0x0000000200101100 0x0000000008004044 0x40cf883e0c7cf3fd 0xbd033e20f831f3cf

def z1227 : W := mkw 0x1fffefbc0000003e 0x007fffbef0000000 0xdffffffe004003d0 0xff7ffffff801000f

def z1228 : W := mkw 0x0ac0dc016c02e821 0x302b037005b00ba0 0xffcffe31fc7fffff 0xffff3ff8c7f1ffff

def z1229 : W := mkw 0x1fbf67bdbb68003f 0xc07efd9ef6eda000 0xffff77fffffc001f 0xdffffddffffff000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z7,z6,z6]),(0,[z1,z8,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z9,z6])],[(0,[z1,z2,z10,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z11,z7,z6])],[(0,[z1,z2,z3,z12,z4,z7,z6]),(0,[z13,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z7,z6,z15]),(0,[z16,z1,z17,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z7,z18,z6]),(0,[z1,z19,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z20,z21,z6]),(0,[z1,z2,z22,z3,z4,z23,z6])],[(0,[z1,z2,z3,z4,z24,z7,z6]),(0,[z25,z1,z2,z3,z4,z5,z6]),(0,[z1,z26,z3,z4,z20,z7,z6]),(0,[z27,z1,z2,z3,z4,z7,z6]),(1,[z1,z2,z3,z28,z7,z6]),(0,[z29,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z30,z3,z4,z14,z6])],[(0,[z1,z2,z3,z4,z31,z7,z6]),(0,[z1,z2,z3,z32,z4,z7,z6]),(0,[z1,z2,z33,z3,z4,z7,z6]),(0,[z34,z35,z2,z3,z4,z7,z6]),(0,[z1,z2,z36,z3,z37,z7,z6]),(0,[z1,z2,z38,z3,z4,z7,z6])],[(1,[z1,z2,z3,z4,z39,z6]),(0,[z1,z2,z3,z4,z21,z6,z40]),(0,[z41,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z42,z7,z6]),(0,[z43,z1,z2,z44,z4,z7,z6])],[(0,[z1,z2,z3,z45,z4,z7,z6]),(0,[z46,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z47,z4,z7,z6]),(1,[z1,z2,z48,z4,z7,z6]),(1,[z1,z2,z3,z49,z7,z6])]],
   [[(0,[z1,z2,z3,z4,z50,z7,z6]),(0,[z1,z2,z3,z51,z4,z7,z6]),(0,[z13,z1,z2,z3,z4,z52,z6]),(0,[z1,z2,z3,z53,z4,z54,z6]),(0,[z1,z2,z3,z4,z7,z55,z6]),(0,[z56,z1,z2,z3,z4,z7,z6]),(0,[z57,z1,z2,z3,z4,z21,z6])],[(0,[z58,z1,z2,z3,z4,z14,z6]),(0,[z25,z1,z2,z3,z59,z7,z6]),(0,[z1,z2,z3,z53,z7,z21,z6]),(0,[z60,z1,z2,z3,z4,z7,z6])],[(0,[z1,z61,z62,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z21,z63,z6]),(0,[z64,z1,z2,z30,z4,z7,z6]),(0,[z1,z2,z3,z4,z65,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z66])],[(0,[z1,z67,z2,z3,z4,z68,z6]),(0,[z1,z2,z3,z4,z69,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z70]),(0,[z1,z26,z2,z3,z4,z14,z6]),(0,[z1,z2,z4,z7,z71,z6,z72]),(0,[z1,z73,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z7,z6,z74]),(0,[z1,z2,z75,z3,z4,z7,z6]),(1,[z13,z2,z3,z76,z7,z6]),(0,[z1,z2,z3,z4,z77,z7,z6]),(0,[z78,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z79,z7,z6]),(0,[z80,z1,z2,z3,z4,z7,z6]),(0,[z1,z81,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z82,z7,z6]),(0,[z1,z2,z83,z3,z4,z7,z6])],[(0,[z84,z1,z2,z3,z4,z7,z6]),(0,[z85,z1,z2,z3,z4,z7,z6]),(1,[z86,z2,z3,z87,z7,z6]),(0,[z1,z2,z3,z88,z4,z7,z6]),(0,[z89,z1,z2,z3,z4,z7,z6]),(0,[z16,z1,z2,z3,z4,z7,z90])],[(0,[z1,z2,z91,z3,z4,z14,z6]),(0,[z92,z1,z2,z3,z20,z7,z6]),(0,[z1,z2,z3,z4,z7,z93,z6]),(0,[z1,z2,z3,z7,z21,z90,z6]),(0,[z94,z1,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z7,z6,z95]),(0,[z96,z1,z2,z30,z4,z7,z6]),(0,[z1,z2,z3,z4,z97,z98,z6])]],
   [[(0,[z0,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z7,z99,z6]),(0,[z34,z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z7,z100,z6]),(0,[z64,z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z21,z21,z6])],[(0,[z101,z1,z2,z3,z4,z7,z6]),(0,[z102,z1,z2,z3,z4,z7,z6]),(0,[z103,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z104,z6])],[(0,[z1,z2,z3,z105,z4,z7,z6]),(0,[z1,z2,z3,z4,z54,z7,z6]),(0,[z106,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z107,z4,z14,z6])],[(0,[z108,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z109,z6])],[(0,[z25,z1,z2,z3,z4,z14,z6]),(1,[z1,z2,z3,z110,z7,z6]),(0,[z1,z2,z3,z111,z4,z7,z6])],[(0,[z1,z2,z3,z4,z112,z21,z6]),(0,[z96,z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z113,z21,z6]),(0,[z16,z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z114,z7,z6]),(0,[z1,z2,z3,z4,z7,z115,z6])],[(0,[z1,z2,z3,z4,z4,z7,z6]),(1,[z1,z2,z116,z3,z4,z6]),(0,[z1,z2,z3,z107,z7,z21,z6])],[(0,[z1,z2,z3,z4,z7,z6,z117]),(1,[z1,z2,z3,z118,z7,z6]),(0,[z0,z1,z2,z3,z4,z97,z6]),(0,[z1,z2,z3,z119,z4,z7,z6])]],
   [[(0,[z120,z1,z2,z62,z3,z4,z6]),(0,[z1,z121,z2,z3,z4,z7,z6]),(0,[z122,z1,z2,z3,z4,z7,z6]),(1,[z1,z2,z3,z4,z100,z6]),(0,[z1,z2,z3,z4,z37,z7,z6]),(0,[z123,z1,z2,z3,z4,z7,z6])],[(0,[z124,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z125,z6]),(0,[z0,z2,z3,z4,z5,z7,z6]),(0,[z1,z2,z3,z4,z7,z126,z6]),(0,[z1,z2,z127,z3,z4,z7,z6])],[(0,[z58,z1,z62,z3,z4,z7,z6]),(0,[z1,z2,z128,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z129]),(0,[z1,z130,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z131]),(0,[z1,z2,z3,z4,z68,z6,z132]),(0,[z1,z2,z3,z4,z7,z6,z133])],[(0,[z1,z2,z62,z3,z4,z21,z6]),(0,[z1,z2,z3,z134,z4,z7,z6]),(0,[z25,z1,z2,z3,z4,z97,z6]),(0,[z135,z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z14,z6,z70]),(0,[z1,z136,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z97,z7,z6])],[(1,[z1,z2,z3,z4,z52,z6]),(0,[z1,z2,z3,z137,z4,z7,z6]),(0,[z1,z67,z2,z3,z4,z71,z6]),(0,[z1,z2,z3,z4,z7,z138,z6])],[(0,[z139,z1,z2,z30,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z140]),(0,[z1,z2,z36,z3,z4,z141,z6]),(0,[z1,z2,z22,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z7,z6,z142])],[(0,[z143,z1,z2,z3,z4,z7,z6]),(0,[z144,z2,z62,z3,z4,z7,z6]),(0,[z1,z2,z22,z3,z76,z7,z6]),(0,[z145,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z146]),(0,[z147,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z148,z3,z4,z7,z6]),(0,[z16,z149,z1,z2,z3,z7,z6])],[(0,[z1,z2,z3,z87,z4,z150,z6]),(0,[z151,z1,z2,z3,z4,z7,z6]),(0,[z152,z1,z2,z3,z4,z7,z6]),(0,[z153,z1,z2,z3,z4,z7,z6])]],
   [[(0,[z85,z1,z2,z4,z7,z6,z72]),(0,[z1,z2,z3,z4,z21,z154,z6])],[(0,[z1,z2,z3,z4,z7,z155,z6]),(0,[z1,z2,z3,z156,z4,z7,z6])],[(0,[z1,z2,z3,z4,z157,z7,z6]),(0,[z1,z2,z3,z4,z158,z71,z6]),(0,[z1,z2,z3,z4,z159,z7,z6]),(0,[z1,z2,z4,z37,z7,z6,z72]),(1,[z160,z1,z2,z4,z161,z6])],[(0,[z139,z1,z2,z3,z4,z21,z6]),(0,[z86,z1,z2,z3,z76,z7,z6]),(0,[z1,z2,z3,z4,z7,z162,z6]),(0,[z1,z2,z3,z4,z28,z7,z6]),(0,[z1,z2,z163,z3,z4,z7,z6]),(0,[z164,z1,z2,z3,z4,z7,z6])],[(1,[z120,z1,z2,z3,z4,z6]),(0,[z1,z61,z2,z3,z4,z21,z6]),(0,[z165,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z14,z68,z6])],[(0,[z1,z166,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z87,z4,z7,z6])],[(0,[z167,z1,z2,z3,z4,z7,z6]),(0,[z168,z1,z3,z169,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z98,z6]),(0,[z1,z2,z3,z4,z49,z7,z6])],[(0,[z170,z1,z2,z3,z4,z7,z6]),(0,[z171,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z172,z3,z4,z7,z6]),(0,[z173,z1,z2,z3,z4,z161,z6]),(0,[z1,z2,z3,z4,z21,z174,z6])]],
   [[(0,[z1,z2,z3,z175,z4,z7,z6]),(0,[z1,z2,z176,z3,z4,z7,z6]),(0,[z1,z177,z2,z3,z7,z6,z70]),(0,[z1,z2,z3,z178,z4,z7,z6]),(0,[z1,z2,z179,z3,z4,z7,z6]),(0,[z1,z2,z3,z180,z4,z7,z6]),(0,[z181,z1,z2,z3,z4,z7,z6])],[(1,[z1,z2,z3,z31,z7,z6]),(0,[z1,z2,z3,z4,z182,z7,z6]),(0,[z1,z2,z3,z4,z7,z183,z6])],[(0,[z1,z2,z184,z3,z4,z7,z6]),(0,[z185,z1,z2,z3,z4,z7,z6])],[(0,[z139,z1,z2,z186,z4,z7,z6]),(0,[z1,z187,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z188,z7,z6]),(0,[z168,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z189,z6]),(0,[z190,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z191,z6]),(0,[z1,z2,z3,z4,z7,z192,z6]),(0,[z1,z2,z3,z193,z7,z90,z6])],[(0,[z85,z1,z2,z3,z4,z14,z6]),(1,[z1,z2,z4,z7,z6,z194]),(0,[z1,z2,z195,z3,z4,z7,z6]),(1,[z1,z2,z196,z4,z71,z6])],[(0,[z197,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z198,z6]),(0,[z1,z2,z199,z3,z4,z21,z6])],[(0,[z200,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z150,z7,z6]),(1,[z1,z2,z36,z37,z7,z6]),(0,[z1,z201,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z202])],[(0,[z1,z203,z3,z169,z4,z7,z6]),(0,[z168,z1,z61,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z204,z6]),(1,[z16,z1,z2,z3,z21,z6])]],
   [[(1,[z1,z2,z3,z4,z50,z6]),(0,[z1,z205,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z206]),(0,[z34,z1,z3,z4,z7,z6,z70]),(0,[z1,z2,z3,z4,z207,z7,z6])],[(0,[z208,z1,z2,z3,z4,z7,z6])],[(0,[z1,z2,z209,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z7,z6]),(0,[z1,z130,z3,z4,z20,z7,z6]),(0,[z1,z2,z3,z4,z210,z7,z6]),(1,[z43,z1,z2,z3,z4,z132])],[(0,[z1,z2,z3,z211,z4,z7,z6])],[(0,[z1,z203,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z212,z4,z7,z6]),(0,[z1,z2,z213,z3,z4,z7,z6]),(1,[z1,z2,z3,z4,z150,z6]),(0,[z144,z1,z2,z3,z4,z14,z6]),(1,[z1,z2,z3,z4,z159,z6]),(0,[z1,z130,z2,z3,z53,z7,z6]),(0,[z92,z1,z26,z3,z4,z7,z6]),(0,[z1,z2,z214,z3,z4,z7,z6])],[(1,[z1,z215,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z216]),(0,[z1,z2,z3,z4,z7,z6,z217]),(0,[z1,z2,z3,z4,z218,z7,z6]),(0,[z1,z2,z3,z4,z14,z71,z6]),(1,[z1,z2,z3,z4,z219,z6]),(0,[z1,z2,z3,z4,z98,z6,z132])],[(0,[z1,z220,z2,z3,z4,z7,z6]),(0,[z43,z1,z67,z2,z3,z4,z6]),(0,[z1,z26,z2,z3,z4,z21,z6]),(0,[z1,z2,z4,z7,z221,z6,z72]),(0,[z222,z1,z2,z3,z4,z7,z6])],[(0,[z1,z2,z223,z62,z3,z4,z6]),(0,[z1,z2,z3,z4,z37,z14,z6]),(0,[z1,z224,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z225,z4,z7,z6]),(0,[z226,z1,z2,z3,z4,z7,z6]),(0,[z227,z1,z2,z3,z4,z7,z6])]],
   [[(1,[z58,z62,z3,z4,z7,z6]),(0,[z228,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z229,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z158,z6]),(0,[z1,z2,z3,z4,z230,z7,z6]),(0,[z1,z2,z3,z4,z231,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z232])],[(0,[z139,z1,z2,z3,z4,z233,z6]),(0,[z1,z2,z3,z186,z4,z14,z6]),(0,[z1,z2,z91,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z21,z234,z6]),(0,[z1,z2,z3,z235,z4,z7,z6]),(0,[z1,z130,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z236,z7,z6])],[(1,[z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z5,z21,z6]),(0,[z1,z2,z3,z4,z7,z6,z237]),(0,[z238,z1,z2,z3,z4,z7,z6]),(0,[z1,z3,z53,z4,z20,z7,z6]),(0,[z173,z1,z2,z3,z4,z98,z6]),(0,[z1,z2,z3,z4,z14,z65,z6])],[(0,[z239,z1,z2,z3,z4,z7,z6]),(0,[z0,z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z240,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z132])],[(1,[z208,z1,z2,z4,z7,z6]),(0,[z1,z241,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z242,z4,z7,z6]),(0,[z243,z1,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z7,z234,z72]),(0,[z244,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z169,z4,z7,z6,z72]),(0,[z245,z1,z2,z3,z4,z7,z6]),(0,[z246,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z107,z4,z21,z6]),(0,[z143,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z247,z7,z6])],[(1,[z1,z2,z10,z4,z7,z6]),(0,[z1,z2,z3,z248,z4,z7,z6]),(0,[z1,z249,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z221,z6]),(0,[z1,z2,z3,z4,z7,z6,z250])],[(0,[z25,z1,z2,z3,z4,z21,z6]),(1,[z1,z2,z3,z4,z23,z6]),(0,[z1,z251,z2,z3,z4,z7,z6])]],
   [[(0,[z1,z61,z2,z252,z4,z7,z6]),(0,[z92,z1,z2,z3,z7,z90,z6]),(0,[z1,z2,z3,z4,z21,z6,z253]),(0,[z254,z1,z2,z3,z4,z7,z6])],[(0,[z255,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z39,z6])],[(0,[z1,z2,z256,z3,z4,z7,z6]),(0,[z168,z1,z2,z169,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z257,z6])],[(0,[z258,z1,z2,z3,z4,z7,z6]),(0,[z1,z259,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z260,z6])],[(0,[z1,z2,z3,z4,z261,z7,z6]),(0,[z1,z2,z3,z87,z4,z14,z6]),(0,[z1,z2,z3,z59,z4,z7,z6]),(0,[z1,z2,z3,z262,z4,z7,z6]),(0,[z1,z2,z263,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z264,z6]),(0,[z1,z265,z2,z3,z4,z7,z6])],[(0,[z266,z1,z2,z3,z4,z7,z6]),(0,[z135,z1,z2,z3,z4,z7,z234]),(0,[z1,z267,z2,z3,z4,z7,z6]),(0,[z160,z1,z2,z3,z4,z71,z6]),(0,[z1,z2,z3,z4,z7,z6,z268])],[(0,[z269,z1,z2,z3,z4,z21,z6]),(0,[z13,z1,z2,z3,z76,z7,z6]),(1,[z25,z2,z3,z4,z158,z6]),(0,[z144,z1,z2,z3,z4,z7,z234]),(0,[z1,z2,z3,z4,z7,z270,z6]),(0,[z271,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z53,z7,z6,z272]),(0,[z173,z1,z2,z3,z4,z7,z6]),(0,[z1,z67,z2,z3,z110,z7,z6]),(1,[z1,z2,z273,z4,z7,z6]),(0,[z1,z2,z36,z3,z4,z7,z6])],[(0,[z274,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z275,z6]),(0,[z276,z1,z2,z3,z4,z7,z6]),(0,[z149,z1,z2,z3,z4,z7,z6])]],
   [[(0,[z1,z2,z22,z3,z4,z21,z6]),(1,[z1,z2,z3,z4,z277,z6])],[(0,[z1,z2,z3,z4,z7,z278,z6]),(0,[z139,z1,z2,z91,z4,z7,z6]),(1,[z1,z2,z3,z4,z7,z279]),(0,[z1,z2,z3,z4,z7,z280,z6]),(0,[z1,z2,z3,z4,z7,z281,z6]),(0,[z1,z2,z3,z4,z282,z7,z6]),(0,[z173,z1,z2,z3,z4,z112,z6]),(0,[z283,z1,z2,z3,z4,z7,z6])],[(0,[z168,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z21,z284,z6]),(0,[z1,z2,z3,z4,z7,z285,z6])],[(0,[z1,z2,z286,z3,z4,z7,z6]),(0,[z1,z2,z3,z134,z186,z4,z6]),(0,[z1,z2,z3,z4,z7,z287,z6]),(1,[z1,z2,z3,z4,z288,z6])],[(0,[z289,z1,z2,z3,z4,z7,z6])],[(0,[z86,z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z7,z6,z290]),(0,[z1,z67,z2,z3,z4,z161,z6]),(0,[z291,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z116,z3,z4,z6,z70]),(0,[z1,z2,z3,z292,z4,z7,z6]),(0,[z1,z293,z2,z3,z4,z7,z6])],[(1,[z1,z2,z3,z59,z7,z6]),(0,[z294,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z14,z221,z6])],[(1,[z1,z177,z2,z3,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z295]),(0,[z1,z2,z3,z4,z207,z14,z6]),(0,[z1,z2,z3,z4,z14,z6,z272])]],
   [[(0,[z34,z296,z2,z3,z4,z7,z6]),(1,[z1,z2,z30,z4,z7,z221])],[(0,[z1,z2,z3,z4,z297,z7,z6]),(0,[z1,z2,z298,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z7,z6,z299]),(0,[z1,z2,z3,z300,z4,z7,z6]),(0,[z301,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z302,z7,z6])],[(0,[z1,z203,z2,z3,z4,z14,z6]),(0,[z43,z1,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z303,z7,z6]),(1,[z135,z2,z3,z4,z7,z40]),(1,[z1,z2,z3,z4,z141,z6]),(0,[z1,z304,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z305,z7,z6])],[(0,[z1,z306,z2,z3,z4,z7,z6]),(0,[z1,z2,z307,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z308,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z72]),(0,[z16,z1,z2,z48,z4,z7,z6])],[(0,[z1,z2,z3,z4,z309,z7,z6]),(0,[z1,z2,z3,z4,z310,z7,z6]),(0,[z1,z2,z3,z4,z311,z7,z6]),(0,[z1,z2,z3,z4,z7,z312,z6])],[(0,[z1,z2,z3,z4,z7,z313,z6])]],
   [[(0,[z1,z2,z3,z4,z314,z7,z6]),(0,[z1,z2,z3,z4,z7,z315,z6])],[(0,[z1,z2,z3,z169,z4,z7,z6]),(0,[z1,z2,z252,z4,z7,z6,z72]),(0,[z316,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z317]),(1,[z1,z2,z3,z4,z14,z6])],[(0,[z1,z2,z3,z318,z4,z7,z6]),(1,[z139,z2,z186,z4,z7,z6]),(0,[z319,z1,z2,z3,z4,z7,z6]),(0,[z96,z1,z2,z3,z4,z7,z221])],[(0,[z320,z1,z2,z3,z4,z7,z6]),(0,[z321,z1,z2,z3,z4,z7,z6]),(0,[z1,z322,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z100,z6,z70]),(0,[z1,z2,z3,z4,z323,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z324]),(0,[z1,z2,z3,z4,z7,z6,z325])],[(0,[z85,z1,z61,z2,z4,z7,z6]),(0,[z1,z2,z326,z3,z4,z7,z6]),(1,[z1,z2,z3,z4,z54,z6])],[(0,[z1,z2,z3,z4,z7,z327,z6]),(0,[z328,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z5,z71,z6])],[(0,[z2,z62,z3,z4,z7,z6,z40]),(0,[z1,z329,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z330,z7,z6]),(0,[z1,z2,z3,z4,z7,z331,z6]),(0,[z332,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z333,z4,z7,z6]),(1,[z1,z2,z3,z4,z312,z6])],[(0,[z1,z2,z334,z3,z4,z7,z6]),(0,[z139,z168,z1,z2,z4,z7,z6]),(0,[z144,z1,z2,z3,z4,z21,z6]),(1,[z1,z2,z3,z4,z313,z6]),(0,[z1,z2,z335,z3,z4,z7,z6]),(0,[z1,z2,z196,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z114,z21,z6]),(0,[z254,z1,z2,z3,z4,z14,z6])]],
   [[(0,[z86,z2,z3,z87,z4,z7,z6]),(0,[z1,z2,z3,z87,z4,z336,z6]),(0,[z1,z67,z2,z3,z4,z98,z6]),(0,[z1,z2,z3,z4,z7,z6,z337]),(0,[z1,z2,z338,z3,z4,z7,z6]),(1,[z64,z1,z2,z22,z7,z6]),(0,[z1,z2,z3,z339,z4,z7,z6]),(1,[z1,z2,z3,z21,z90,z6]),(1,[z1,z2,z3,z4,z315,z6])],[(0,[z1,z2,z3,z4,z7,z340,z6]),(0,[z149,z1,z2,z3,z53,z7,z6]),(0,[z173,z1,z67,z3,z4,z7,z6])],[(0,[z341,z1,z2,z3,z4,z7,z6]),(0,[z1,z342,z2,z3,z4,z7,z6]),(0,[z343,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z37,z21,z6])],[(0,[z208,z1,z2,z62,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z344]),(0,[z345,z1,z2,z3,z4,z7,z6]),(0,[z96,z1,z2,z3,z4,z7,z72])],[(0,[z1,z2,z3,z186,z4,z21,z6]),(0,[z1,z130,z2,z3,z4,z21,z6]),(0,[z346,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z97,z7,z98]),(0,[z1,z2,z3,z347,z4,z7,z6])],[(1,[z1,z2,z3,z87,z21,z6]),(0,[z25,z2,z3,z4,z7,z158,z6]),(0,[z1,z2,z3,z53,z4,z348,z6]),(0,[z1,z2,z3,z4,z21,z68,z6]),(0,[z173,z1,z2,z3,z4,z14,z6]),(1,[z1,z2,z3,z4,z349,z6]),(0,[z1,z2,z36,z3,z4,z14,z6]),(0,[z350,z1,z2,z3,z4,z7,z6]),(0,[z160,z1,z2,z4,z7,z6,z72]),(0,[z1,z2,z3,z4,z97,z21,z6]),(0,[z1,z2,z3,z4,z351,z7,z6])],[(0,[z1,z2,z3,z4,z7,z6,z352]),(0,[z353,z1,z2,z3,z4,z7,z6]),(0,[z1,z354,z2,z3,z4,z7,z6]),(1,[z1,z2,z3,z111,z7,z6]),(0,[z1,z2,z3,z4,z355,z7,z6]),(0,[z1,z2,z3,z4,z14,z161,z6]),(0,[z1,z2,z3,z4,z7,z6,z356]),(0,[z1,z2,z3,z4,z7,z6,z357]),(0,[z149,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z7,z6,z358])],[(0,[z359,z1,z2,z3,z4,z7,z6]),(0,[z149,z1,z2,z3,z76,z7,z6]),(1,[z144,z2,z3,z4,z7,z234]),(1,[z1,z2,z3,z4,z310,z6])]],
   [[(0,[z269,z203,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z360,z4,z7,z6]),(0,[z361,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z362,z6]),(0,[z1,z2,z3,z4,z14,z115,z6])],[(0,[z120,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z363,z3,z4,z7,z6]),(0,[z364,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z365,z6]),(0,[z1,z2,z366,z3,z4,z7,z6])],[(0,[z139,z1,z209,z3,z4,z7,z6]),(0,[z173,z25,z1,z2,z3,z4,z6])],[(0,[z92,z1,z2,z3,z4,z7,z6]),(0,[z367,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z368,z7,z6]),(1,[z1,z2,z3,z193,z7,z90])],[(0,[z369,z1,z2,z3,z4,z7,z6]),(0,[z1,z67,z2,z3,z4,z7,z6]),(1,[z173,z1,z3,z4,z112,z6]),(0,[z1,z370,z2,z3,z4,z7,z6])],[(0,[z371,z1,z2,z3,z4,z7,z6]),(0,[z372,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z76,z7,z21,z6]),(0,[z92,z1,z3,z53,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z373])],[(0,[z1,z2,z3,z4,z374,z7,z6]),(0,[z16,z1,z2,z3,z7,z6,z272])],[(0,[z1,z2,z3,z87,z4,z21,z6]),(0,[z1,z2,z3,z4,z7,z221,z234]),(0,[z1,z67,z2,z3,z4,z112,z6])]],
   [[(0,[z375,z1,z2,z3,z4,z7,z6]),(0,[z13,z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z376,z7,z6]),(0,[z173,z1,z3,z4,z112,z7,z6]),(0,[z377,z1,z2,z3,z4,z7,z6])],[(0,[z1,z2,z378,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z379,z6]),(0,[z1,z2,z3,z4,z380,z7,z6]),(0,[z1,z2,z381,z3,z4,z7,z6])],[(0,[z86,z13,z2,z3,z4,z7,z6]),(0,[z1,z2,z30,z3,z4,z21,z6])],[(1,[z1,z2,z382,z4,z7,z6]),(0,[z149,z1,z2,z3,z14,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z383])],[(0,[z1,z2,z3,z4,z384,z7,z6]),(0,[z1,z2,z3,z4,z7,z385,z6])],[(0,[z266,z1,z2,z3,z186,z4,z6]),(1,[z1,z2,z3,z4,z336,z6]),(0,[z0,z160,z1,z2,z3,z4,z6]),(0,[z168,z1,z2,z3,z4,z21,z6]),(0,[z386,z1,z2,z3,z4,z7,z6]),(1,[z1,z387,z3,z4,z7,z6])],[(0,[z388,z1,z2,z3,z4,z7,z6]),(0,[z389,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z63,z6]),(0,[z1,z177,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z21,z71,z6]),(0,[z160,z1,z2,z3,z4,z161,z6])],[(0,[z58,z1,z2,z3,z4,z21,z6]),(0,[z85,z2,z91,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z194]),(0,[z1,z2,z3,z20,z7,z21,z6])]],
   [[(0,[z390,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z30,z4,z37,z7,z6]),(0,[z1,z2,z3,z4,z4,z14,z6]),(0,[z1,z391,z2,z3,z4,z7,z6])],[(0,[z392,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z76,z7,z6]),(0,[z1,z2,z3,z393,z4,z7,z6]),(0,[z394,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z395,z7,z6]),(1,[z35,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z396,z4,z7,z6]),(0,[z1,z2,z3,z4,z14,z98,z6])],[(0,[z1,z2,z3,z397,z4,z7,z6]),(0,[z1,z130,z2,z3,z20,z7,z6]),(0,[z1,z2,z3,z14,z7,z21,z6])],[(0,[z57,z1,z2,z3,z4,z7,z6]),(0,[z34,z1,z2,z3,z4,z398,z6]),(0,[z1,z2,z3,z4,z7,z6,z399])],[(0,[z400,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z21,z6])],[(0,[z401,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z402,z7,z6]),(0,[z1,z2,z3,z403,z4,z7,z6]),(0,[z1,z2,z3,z4,z161,z7,z6]),(0,[z1,z2,z30,z3,z4,z7,z72])],[(0,[z1,z2,z3,z4,z404,z7,z6]),(0,[z1,z2,z405,z3,z4,z7,z6])],[(0,[z1,z406,z2,z3,z4,z7,z6]),(0,[z407,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z408,z4,z7,z6]),(0,[z1,z2,z3,z4,z21,z90,z6])]],
   [[(0,[z1,z2,z409,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z410]),(0,[z1,z2,z3,z4,z7,z6,z411])],[(0,[z1,z2,z412,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z413])],[(1,[z266,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z7,z414,z6])],[(0,[z1,z2,z3,z118,z4,z7,z6]),(0,[z1,z2,z3,z4,z161,z158,z6]),(0,[z1,z2,z3,z415,z4,z7,z6]),(0,[z1,z2,z252,z3,z4,z159,z6]),(0,[z1,z2,z48,z3,z4,z7,z6])],[(0,[z1,z2,z3,z416,z4,z7,z6]),(0,[z417,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z418]),(1,[z1,z2,z3,z7,z6,z337]),(0,[z419,z1,z2,z3,z4,z7,z6]),(1,[z1,z2,z3,z4,z21,z6]),(1,[z1,z2,z420,z4,z7,z6])],[(0,[z1,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z421,z4,z7,z6]),(0,[z1,z2,z3,z3,z4,z7,z6]),(0,[z139,z1,z2,z3,z31,z7,z6]),(0,[z422,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z423,z7,z6]),(0,[z424,z1,z2,z3,z4,z7,z6]),(0,[z64,z1,z2,z3,z37,z7,z6]),(0,[z1,z2,z425,z3,z4,z7,z6]),(0,[z1,z2,z30,z4,z7,z71,z6]),(0,[z1,z2,z3,z4,z14,z7,z6]),(0,[z1,z2,z3,z4,z14,z374,z6])],[(0,[z1,z2,z3,z4,z7,z426,z6]),(0,[z135,z1,z2,z3,z4,z7,z40])],[(0,[z144,z1,z2,z3,z4,z7,z40]),(0,[z1,z2,z3,z7,z6,z337,z70])]],
   [[(0,[z1,z2,z3,z4,z7,z427,z6]),(0,[z1,z2,z3,z4,z14,z112,z6]),(0,[z96,z1,z2,z3,z4,z428,z6]),(0,[z16,z1,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z429,z7,z6]),(0,[z2,z91,z3,z186,z4,z7,z6]),(0,[z1,z2,z3,z4,z52,z7,z6]),(0,[z1,z2,z252,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z430,z6]),(0,[z1,z2,z22,z36,z3,z7,z6]),(0,[z431,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z14,z432,z6])],[(0,[z1,z2,z3,z4,z433,z7,z6]),(0,[z434,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z196,z3,z4,z21,z6]),(0,[z367,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z435,z7,z6])],[(0,[z1,z62,z3,z169,z4,z7,z6]),(0,[z1,z2,z3,z87,z7,z21,z6]),(0,[z1,z2,z3,z4,z14,z158,z6]),(0,[z1,z2,z3,z4,z7,z6,z436]),(0,[z1,z67,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z437,z7,z6]),(0,[z1,z2,z3,z7,z90,z6,z272]),(0,[z1,z438,z2,z3,z4,z7,z6]),(0,[z1,z439,z2,z3,z4,z7,z6])],[(0,[z139,z1,z2,z3,z4,z50,z6]),(0,[z1,z2,z3,z4,z440,z7,z6]),(0,[z1,z2,z3,z441,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z154,z6])],[(0,[z1,z2,z3,z4,z442,z7,z6]),(0,[z443,z1,z2,z3,z4,z7,z6]),(0,[z160,z1,z2,z4,z161,z7,z6]),(0,[z1,z8,z2,z3,z4,z21,z6])],[(0,[z1,z2,z62,z3,z4,z7,z6]),(0,[z25,z1,z2,z3,z444,z7,z6]),(0,[z1,z2,z30,z252,z4,z7,z6]),(0,[z1,z2,z3,z4,z14,z6,z132]),(0,[z1,z2,z3,z445,z4,z7,z6])],[(0,[z446,z1,z2,z3,z4,z7,z6]),(0,[z34,z1,z26,z3,z4,z7,z6])]],
   [[(0,[z447,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z448,z3,z4,z7,z6]),(0,[z173,z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z7,z6,z449]),(0,[z34,z1,z2,z3,z28,z7,z6]),(0,[z1,z2,z36,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z21,z6,z272])],[(0,[z1,z450,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z451,z4,z7,z6]),(0,[z1,z2,z3,z273,z4,z7,z6]),(0,[z34,z1,z2,z3,z4,z7,z63]),(0,[z1,z2,z22,z4,z37,z7,z6]),(0,[z149,z1,z2,z3,z4,z21,z6]),(0,[z452,z1,z2,z3,z4,z7,z6]),(1,[z94,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z53,z193,z7,z6]),(0,[z1,z2,z3,z4,z453,z7,z6]),(1,[z1,z2,z298,z4,z7,z6])],[(0,[z1,z2,z3,z4,z7,z174,z6]),(0,[z454,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z42,z21,z6])],[(0,[z85,z1,z2,z30,z4,z7,z6]),(0,[z1,z2,z455,z3,z4,z7,z6]),(0,[z456,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z14,z5,z6]),(0,[z1,z2,z3,z457,z4,z7,z6]),(0,[z1,z458,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z21,z9,z6])],[(0,[z1,z2,z3,z4,z7,z459,z6]),(0,[z460,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z461,z7,z6]),(0,[z160,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z193,z4,z7,z272])],[(0,[z462,z1,z2,z3,z4,z7,z6]),(0,[z463,z1,z2,z3,z4,z7,z6]),(0,[z139,z1,z2,z3,z4,z7,z6]),(0,[z464,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z465,z3,z4,z7,z6]),(0,[z296,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z36,z4,z37,z7,z6]),(0,[z64,z1,z2,z4,z7,z6,z72]),(0,[z60,z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z466,z7,z6])],[(0,[z1,z2,z467,z3,z4,z7,z6]),(0,[z1,z391,z2,z3,z4,z14,z6])]],
   [[(0,[z1,z2,z3,z4,z76,z14,z6]),(0,[z1,z2,z3,z4,z7,z468,z6]),(0,[z64,z1,z2,z22,z3,z7,z6])],[(1,[z1,z2,z223,z3,z4,z6]),(0,[z1,z2,z3,z4,z469,z7,z6]),(0,[z1,z470,z2,z3,z4,z7,z6]),(0,[z1,z2,z471,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z472,z7,z6]),(0,[z1,z2,z3,z193,z4,z7,z6]),(0,[z16,z1,z2,z3,z4,z288,z6]),(0,[z1,z2,z3,z4,z97,z7,z132])],[(0,[z85,z1,z2,z3,z4,z21,z6])],[(0,[z473,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z474]),(0,[z475,z1,z2,z3,z4,z7,z6]),(0,[z96,z1,z2,z4,z7,z6,z72])],[(0,[z1,z2,z22,z3,z87,z7,z6]),(0,[z1,z67,z3,z4,z7,z68,z6]),(0,[z1,z2,z3,z4,z476,z7,z6]),(0,[z1,z2,z477,z3,z4,z7,z6]),(0,[z478,z1,z2,z3,z4,z7,z6])],[(1,[z1,z2,z3,z4,z7,z344]),(0,[z1,z2,z3,z4,z479,z7,z6]),(0,[z1,z2,z480,z3,z4,z7,z6]),(0,[z1,z2,z196,z4,z7,z71,z6]),(0,[z1,z2,z3,z97,z49,z7,z6])],[(0,[z1,z2,z3,z481,z4,z7,z6]),(1,[z1,z2,z3,z53,z21,z6]),(0,[z1,z2,z30,z4,z7,z221,z6])],[(0,[z1,z2,z3,z4,z482,z7,z6]),(0,[z1,z2,z3,z4,z21,z6,z70]),(0,[z1,z2,z483,z3,z4,z7,z6]),(0,[z245,z1,z2,z3,z4,z14,z6]),(0,[z484,z1,z2,z3,z4,z7,z6]),(0,[z43,z1,z2,z3,z4,z6,z132])]],
   [[(0,[z1,z485,z2,z3,z4,z7,z6])],[(0,[z1,z2,z2,z3,z4,z7,z6]),(0,[z86,z1,z2,z3,z87,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z486]),(0,[z1,z2,z487,z3,z4,z7,z6]),(0,[z1,z2,z488,z3,z4,z7,z6]),(1,[z489,z2,z3,z4,z7,z6])],[(0,[z85,z1,z2,z186,z4,z7,z6]),(0,[z168,z85,z1,z2,z4,z7,z6]),(0,[z1,z2,z490,z3,z4,z7,z6]),(0,[z1,z130,z2,z3,z4,z491,z6]),(0,[z1,z2,z3,z4,z7,z6,z492]),(0,[z1,z2,z3,z4,z493,z7,z6])],[(0,[z494,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z53,z4,z7,z6]),(0,[z1,z2,z3,z4,z71,z6,z132]),(0,[z1,z2,z3,z4,z161,z97,z6]),(0,[z1,z2,z3,z4,z4,z21,z6]),(0,[z1,z2,z3,z4,z7,z6,z495])],[(0,[z496,z1,z2,z3,z4,z7,z6]),(0,[z1,z3,z4,z20,z7,z6,z70]),(0,[z497,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z498,z7,z6]),(0,[z1,z2,z3,z4,z14,z14,z6])],[(0,[z1,z2,z3,z4,z7,z6,z499]),(0,[z1,z2,z3,z4,z7,z234,z6]),(0,[z1,z2,z500,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z501,z7,z6]),(0,[z16,z1,z130,z2,z3,z7,z6]),(0,[z502,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z503,z3,z4,z7,z6]),(0,[z1,z2,z3,z504,z4,z7,z6])],[],[(0,[z1,z2,z3,z4,z7,z6,z505]),(0,[z1,z2,z3,z4,z506,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z507]),(0,[z149,z1,z2,z3,z20,z7,z6]),(0,[z1,z508,z2,z3,z4,z7,z6]),(0,[z509,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z510,z4,z7,z6]),(0,[z1,z2,z3,z193,z4,z277,z6])]],
   [[(0,[z511,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z252,z3,z4,z14,z6]),(0,[z512,z1,z2,z3,z4,z7,z6]),(0,[z513,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z22,z3,z4,z514,z6]),(0,[z1,z2,z3,z4,z14,z6,z72])],[(0,[z139,z1,z2,z4,z7,z6,z72]),(0,[z1,z2,z3,z4,z515,z7,z6]),(1,[z1,z2,z3,z4,z97,z98])],[(0,[z1,z2,z516,z3,z4,z7,z6]),(0,[z1,z517,z2,z3,z4,z7,z6]),(0,[z16,z92,z1,z2,z3,z7,z6]),(1,[z1,z2,z44,z4,z7,z6])],[(0,[z1,z2,z3,z4,z7,z6,z518]),(0,[z1,z2,z3,z4,z519,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z520]),(0,[z1,z3,z4,z7,z63,z6,z70]),(0,[z1,z2,z3,z521,z4,z7,z6]),(0,[z145,z1,z2,z3,z4,z21,z6]),(0,[z143,z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z14,z97,z6])],[(0,[z1,z2,z522,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z523,z6]),(0,[z1,z130,z2,z3,z7,z90,z6]),(0,[z1,z2,z3,z4,z524,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z253]),(1,[z149,z1,z2,z3,z14,z6])],[(0,[z1,z2,z3,z4,z5,z7,z6]),(1,[z1,z2,z3,z403,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z525])],[(0,[z1,z2,z526,z3,z4,z7,z6]),(0,[z1,z2,z3,z527,z4,z7,z6]),(0,[z1,z2,z252,z3,z4,z313,z6]),(0,[z528,z1,z2,z3,z4,z7,z6]),(0,[z16,z1,z2,z3,z4,z315,z6])],[(0,[z269,z1,z203,z3,z4,z7,z6]),(0,[z139,z85,z2,z3,z4,z7,z6]),(0,[z1,z2,z382,z3,z4,z7,z6])]],
   [[(0,[z529,z1,z2,z3,z4,z7,z6]),(0,[z1,z215,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z336,z6]),(0,[z1,z2,z530,z3,z4,z7,z6]),(0,[z0,z1,z2,z196,z3,z4,z6]),(0,[z1,z2,z3,z107,z4,z7,z6]),(0,[z1,z2,z3,z4,z531,z7,z6])],[(0,[z1,z2,z532,z3,z4,z7,z6])],[],[(0,[z533,z1,z2,z3,z4,z7,z6]),(0,[z149,z1,z2,z3,z107,z7,z6])],[(0,[z1,z2,z3,z4,z534,z7,z6]),(0,[z25,z1,z2,z196,z3,z4,z6]),(0,[z2,z3,z4,z7,z234,z6,z40]),(0,[z1,z252,z3,z169,z4,z7,z6]),(0,[z1,z2,z3,z535,z4,z7,z6]),(0,[z1,z2,z3,z4,z536,z7,z6]),(0,[z1,z2,z3,z4,z537,z7,z6]),(0,[z160,z1,z2,z3,z4,z14,z6]),(0,[z538,z1,z2,z3,z4,z7,z6]),(1,[z1,z17,z3,z4,z7,z6])],[(0,[z1,z2,z539,z3,z4,z7,z6]),(0,[z269,z144,z2,z3,z4,z7,z6]),(0,[z139,z1,z2,z3,z4,z14,z6]),(0,[z540,z1,z2,z3,z4,z7,z6]),(0,[z2,z3,z87,z4,z76,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z40]),(0,[z181,z1,z2,z3,z4,z21,z6]),(0,[z43,z1,z2,z3,z4,z14,z6])],[(0,[z139,z1,z2,z3,z118,z7,z6]),(0,[z541,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z284,z6]),(0,[z1,z67,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z542,z7,z6])],[(0,[z1,z2,z116,z3,z4,z7,z6]),(0,[z1,z26,z2,z3,z4,z7,z63]),(0,[z1,z2,z30,z3,z4,z7,z221])]],
   [[(0,[z1,z2,z3,z4,z7,z543,z6]),(0,[z1,z2,z3,z544,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z545,z6]),(0,[z64,z1,z2,z36,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z546,z6]),(0,[z1,z547,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z193,z4,z14,z6])],[(0,[z269,z1,z2,z3,z4,z7,z6]),(0,[z548,z1,z2,z3,z4,z7,z6]),(0,[z160,z25,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z20,z7,z6]),(0,[z1,z2,z3,z4,z277,z7,z6])],[(0,[z1,z2,z3,z4,z7,z549,z6]),(0,[z1,z2,z3,z4,z7,z491,z6]),(0,[z1,z2,z3,z4,z97,z68,z6]),(0,[z1,z2,z3,z4,z21,z98,z6]),(0,[z16,z1,z2,z3,z193,z7,z6]),(0,[z550,z1,z2,z3,z4,z7,z6])],[(0,[z2,z3,z4,z76,z7,z6,z40]),(0,[z1,z2,z3,z4,z551,z7,z6]),(0,[z1,z2,z3,z169,z4,z14,z6]),(0,[z1,z2,z552,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z288,z7,z6])],[(0,[z86,z144,z2,z3,z4,z7,z6]),(0,[z43,z1,z2,z3,z4,z97,z6])],[(0,[z1,z2,z3,z4,z7,z553,z6]),(0,[z1,z2,z554,z3,z4,z7,z6]),(0,[z1,z2,z3,z193,z4,z312,z6]),(0,[z555,z1,z2,z3,z97,z7,z6])],[(0,[z1,z2,z3,z4,z7,z556,z6]),(0,[z135,z2,z3,z4,z7,z6,z40]),(0,[z1,z2,z3,z557,z4,z7,z6]),(0,[z484,z1,z2,z3,z4,z14,z6])],[(0,[z203,z2,z62,z3,z4,z7,z6]),(0,[z1,z2,z3,z558,z4,z7,z6]),(0,[z1,z2,z559,z3,z4,z7,z6])]],
   [[(0,[z58,z269,z2,z3,z4,z7,z6]),(0,[z85,z1,z2,z91,z4,z7,z6]),(0,[z86,z1,z2,z3,z4,z7,z6]),(0,[z560,z1,z2,z3,z4,z7,z6]),(0,[z173,z43,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z7,z6,z561]),(0,[z1,z2,z3,z4,z14,z6,z373]),(0,[z562,z1,z2,z3,z4,z7,z6])],[(0,[z1,z203,z2,z3,z4,z21,z6]),(0,[z1,z26,z3,z4,z7,z63,z6]),(0,[z1,z2,z3,z4,z493,z14,z6]),(0,[z1,z2,z3,z4,z7,z6,z563]),(0,[z1,z2,z3,z4,z7,z6,z564])],[(0,[z1,z2,z565,z3,z4,z7,z6]),(0,[z1,z2,z490,z4,z7,z234,z6]),(0,[z1,z61,z252,z3,z4,z7,z6]),(1,[z1,z2,z3,z4,z491,z6]),(0,[z1,z2,z3,z53,z4,z14,z6]),(0,[z1,z2,z3,z4,z219,z7,z6])],[(1,[z269,z203,z3,z4,z7,z6]),(0,[z1,z566,z2,z3,z4,z7,z6]),(1,[z85,z2,z91,z4,z7,z6]),(0,[z1,z2,z3,z4,z76,z21,z6]),(1,[z1,z2,z490,z4,z7,z6]),(0,[z1,z2,z3,z4,z567,z7,z6]),(0,[z1,z568,z2,z3,z4,z7,z6]),(0,[z16,z1,z387,z3,z4,z7,z6])],[(0,[z13,z1,z2,z3,z87,z7,z6]),(0,[z569,z1,z2,z3,z4,z7,z6]),(0,[z1,z35,z2,z3,z4,z7,z6]),(1,[z296,z2,z3,z4,z7,z6]),(0,[z1,z2,z503,z3,z4,z14,z6])],[(0,[z570,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z14,z6,z40]),(0,[z345,z1,z2,z3,z4,z14,z6]),(0,[z571,z1,z2,z3,z4,z7,z6])],[(0,[z144,z2,z3,z4,z76,z7,z6]),(0,[z1,z2,z3,z76,z37,z7,z6]),(0,[z1,z2,z3,z572,z4,z7,z6]),(0,[z34,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z573,z4,z7,z6]),(0,[z64,z1,z2,z3,z4,z7,z6]),(0,[z96,z1,z2,z3,z4,z219,z6])],[(0,[z1,z2,z3,z4,z7,z6,z574]),(0,[z1,z2,z3,z4,z161,z21,z6]),(0,[z16,z1,z2,z3,z4,z7,z272])]],
   [[(0,[z1,z2,z575,z3,z4,z7,z6]),(0,[z92,z1,z2,z3,z53,z7,z6]),(0,[z1,z2,z3,z4,z515,z14,z6])],[(0,[z576,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z310,z234,z6]),(0,[z577,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z14,z63,z6]),(0,[z1,z2,z3,z4,z161,z6,z132])],[(0,[z1,z2,z3,z4,z7,z279,z6]),(0,[z1,z2,z578,z3,z4,z7,z6]),(0,[z1,z2,z579,z3,z4,z7,z6]),(0,[z1,z580,z2,z3,z4,z7,z6]),(0,[z1,z581,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z519,z14,z6])],[(0,[z1,z2,z223,z3,z4,z7,z6]),(1,[z1,z209,z3,z4,z7,z6]),(0,[z1,z582,z2,z3,z4,z7,z6]),(0,[z583,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z234,z6,z584]),(0,[z1,z2,z3,z4,z112,z7,z6]),(0,[z1,z2,z4,z161,z7,z71,z6]),(0,[z1,z2,z3,z4,z97,z71,z6]),(0,[z96,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z113,z7,z6])],[(0,[z1,z2,z3,z4,z21,z158,z6]),(0,[z1,z585,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z586,z7,z6]),(0,[z1,z2,z3,z587,z4,z7,z6])],[(0,[z2,z3,z4,z5,z7,z158,z6]),(0,[z135,z144,z2,z3,z4,z7,z6]),(0,[z92,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z588,z4,z7,z6]),(0,[z1,z2,z589,z3,z4,z7,z6]),(1,[z96,z1,z2,z4,z7,z72])],[(0,[z590,z1,z2,z3,z4,z7,z6]),(1,[z1,z26,z3,z4,z7,z63]),(0,[z1,z2,z3,z4,z7,z6,z591])],[(0,[z1,z2,z3,z4,z161,z5,z6]),(1,[z168,z1,z169,z4,z7,z6]),(0,[z1,z2,z3,z4,z14,z21,z6]),(0,[z1,z2,z3,z4,z21,z6,z132]),(0,[z1,z2,z3,z420,z4,z7,z6])]],
   [[(0,[z1,z61,z203,z3,z4,z7,z6]),(0,[z592,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z593]),(0,[z594,z1,z2,z3,z4,z7,z6])],[(0,[z595,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z596,z7,z6]),(0,[z135,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z68,z6]),(0,[z34,z1,z2,z3,z4,z7,z70]),(0,[z43,z1,z2,z3,z4,z7,z132])],[(0,[z1,z2,z3,z4,z7,z597,z6]),(0,[z144,z1,z2,z3,z4,z7,z6]),(0,[z34,z1,z2,z273,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z598,z6]),(0,[z1,z2,z3,z4,z141,z7,z6]),(0,[z1,z2,z3,z4,z21,z221,z6]),(0,[z599,z1,z2,z3,z4,z7,z6]),(0,[z16,z1,z2,z420,z4,z7,z6])],[(1,[z1,z2,z3,z444,z7,z6]),(0,[z600,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z252,z3,z4,z21,z6]),(1,[z1,z130,z3,z20,z7,z6])],[(0,[z139,z1,z215,z3,z4,z7,z6]),(0,[z0,z1,z67,z2,z3,z4,z6]),(0,[z168,z1,z2,z252,z4,z7,z6]),(0,[z1,z130,z2,z3,z4,z501,z6]),(0,[z1,z2,z3,z4,z112,z6,z132]),(0,[z1,z2,z3,z601,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z602]),(0,[z603,z1,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z7,z233,z6]),(0,[z1,z2,z3,z604,z4,z7,z6]),(0,[z1,z2,z3,z4,z605,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z606]),(1,[z92,z1,z3,z53,z7,z6]),(0,[z92,z1,z3,z4,z7,z6,z70]),(0,[z1,z2,z3,z4,z7,z6,z607]),(0,[z1,z2,z3,z4,z7,z6,z608]),(0,[z609,z1,z2,z3,z4,z7,z6])],[(0,[z610,z1,z2,z3,z4,z7,z6]),(0,[z1,z611,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z612]),(0,[z1,z2,z3,z4,z613,z7,z6])],[(0,[z614,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z186,z4,z7,z6]),(0,[z1,z2,z3,z4,z615,z7,z6]),(0,[z13,z2,z3,z4,z76,z7,z6]),(0,[z1,z2,z3,z4,z616,z7,z6]),(0,[z160,z1,z2,z196,z4,z7,z6])]],
   [[(0,[z1,z2,z3,z617,z4,z7,z6]),(0,[z269,z1,z2,z3,z4,z14,z6]),(0,[z25,z1,z67,z2,z3,z4,z6]),(0,[z1,z2,z618,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z619,z6]),(0,[z620,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z621,z7,z6]),(0,[z1,z2,z3,z4,z20,z14,z6])],[(0,[z1,z2,z3,z622,z4,z7,z6]),(0,[z160,z1,z2,z30,z4,z7,z6]),(0,[z149,z1,z2,z3,z7,z90,z6])],[(0,[z623,z1,z2,z3,z4,z7,z6]),(0,[z1,z61,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z349,z7,z6]),(1,[z1,z2,z3,z4,z598,z6]),(0,[z1,z2,z3,z4,z624,z7,z6]),(0,[z1,z2,z3,z4,z7,z625,z6]),(0,[z626,z1,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z7,z627,z6]),(0,[z1,z2,z3,z193,z4,z7,z90]),(0,[z1,z2,z3,z4,z7,z6,z628])],[(0,[z1,z2,z3,z4,z7,z514,z6]),(0,[z1,z2,z387,z3,z4,z7,z6])],[(1,[z1,z2,z3,z4,z233,z6]),(0,[z1,z629,z2,z3,z4,z7,z6]),(0,[z1,z2,z4,z7,z234,z6,z194]),(0,[z630,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z631,z7,z6])],[(0,[z1,z2,z3,z4,z632,z7,z6]),(0,[z1,z2,z3,z633,z4,z7,z6]),(0,[z634,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z196,z3,z4,z161,z6])],[(0,[z86,z1,z2,z3,z4,z14,z6]),(0,[z1,z67,z2,z3,z403,z7,z6]),(0,[z1,z635,z2,z3,z4,z7,z6]),(0,[z160,z1,z2,z3,z4,z21,z6]),(0,[z16,z94,z2,z3,z4,z7,z6]),(0,[z43,z1,z2,z3,z4,z7,z98])]],
   [[(0,[z58,z1,z203,z3,z4,z7,z6]),(0,[z636,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z637,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z638,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z639]),(0,[z43,z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z7,z6,z640])],[(0,[z1,z2,z3,z4,z7,z6,z641]),(1,[z16,z1,z2,z3,z7,z272])],[(0,[z642,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z71,z6])],[(0,[z13,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z643,z4,z7,z6]),(0,[z1,z2,z3,z644,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z645]),(0,[z1,z2,z3,z4,z472,z21,z6]),(0,[z1,z2,z3,z193,z4,z21,z6]),(0,[z1,z2,z199,z3,z4,z7,z6])],[(0,[z1,z2,z3,z87,z37,z7,z6]),(0,[z1,z2,z3,z4,z7,z646,z6]),(0,[z1,z2,z647,z3,z4,z7,z6]),(1,[z1,z2,z3,z20,z21,z6]),(1,[z1,z2,z3,z4,z514,z6]),(0,[z1,z2,z648,z3,z4,z7,z6])],[(0,[z139,z1,z61,z2,z4,z7,z6]),(0,[z149,z1,z2,z3,z87,z7,z6]),(0,[z173,z1,z2,z3,z4,z68,z6]),(0,[z34,z1,z2,z3,z4,z14,z6]),(0,[z64,z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z23,z7,z6]),(0,[z1,z2,z30,z3,z4,z7,z6]),(0,[z649,z1,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z169,z4,z21,z6]),(0,[z1,z2,z36,z3,z4,z598,z6])],[(0,[z1,z2,z3,z4,z7,z650,z6]),(1,[z1,z2,z3,z76,z21,z6]),(1,[z0,z2,z3,z4,z5,z6]),(0,[z92,z1,z130,z3,z4,z7,z6]),(0,[z1,z2,z3,z651,z4,z7,z6]),(0,[z1,z2,z652,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z398,z6]),(0,[z1,z2,z653,z3,z4,z7,z6])]],
   [[(0,[z139,z1,z2,z3,z4,z7,z279]),(0,[z139,z2,z3,z186,z4,z7,z6]),(0,[z0,z173,z1,z2,z3,z4,z6]),(0,[z654,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z655,z4,z7,z6])],[(0,[z269,z1,z62,z3,z4,z7,z6]),(0,[z269,z2,z3,z4,z7,z6,z40]),(0,[z656,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z21,z6,z72]),(0,[z657,z1,z2,z3,z4,z7,z6])],[(0,[z58,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z658,z7,z6]),(0,[z659,z1,z2,z3,z4,z7,z6]),(0,[z660,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z661,z7,z6]),(0,[z96,z1,z2,z3,z4,z14,z6]),(0,[z16,z1,z2,z3,z4,z14,z6])],[(0,[z1,z2,z662,z3,z4,z7,z6]),(0,[z663,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z90,z6])],[(0,[z1,z2,z3,z4,z664,z7,z6]),(0,[z1,z26,z2,z3,z4,z7,z6]),(0,[z1,z489,z2,z3,z4,z7,z6])],[(1,[z1,z2,z3,z134,z4,z6]),(0,[z1,z2,z3,z4,z7,z6,z665]),(0,[z1,z2,z3,z53,z4,z21,z6]),(0,[z1,z2,z3,z4,z7,z6,z666]),(0,[z667,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z668,z7,z6]),(0,[z1,z17,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z7,z6,z669]),(0,[z670,z1,z2,z3,z4,z7,z6]),(0,[z16,z1,z2,z3,z7,z21,z6]),(0,[z43,z1,z2,z298,z4,z7,z6])],[(0,[z1,z2,z3,z4,z671,z7,z6]),(0,[z1,z2,z91,z3,z4,z7,z6]),(1,[z1,z2,z3,z4,z398,z6]),(0,[z1,z2,z3,z4,z672,z7,z6]),(0,[z1,z2,z3,z4,z7,z428,z6]),(0,[z16,z489,z2,z3,z4,z7,z6])]],
   [[(0,[z1,z2,z10,z62,z4,z7,z6]),(0,[z1,z2,z62,z3,z4,z14,z6]),(0,[z86,z2,z3,z4,z7,z6,z40]),(0,[z135,z1,z2,z3,z4,z14,z6]),(0,[z673,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z110,z7,z6]),(0,[z1,z2,z196,z3,z4,z71,z6]),(1,[z1,z2,z3,z107,z21,z6]),(0,[z1,z2,z3,z674,z4,z7,z6])],[(0,[z0,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z40,z72]),(0,[z1,z61,z2,z169,z4,z7,z6]),(0,[z1,z2,z3,z4,z112,z97,z6]),(0,[z34,z1,z2,z3,z4,z349,z6]),(0,[z1,z2,z3,z4,z7,z675,z6]),(0,[z509,z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z432,z7,z6])],[(0,[z13,z1,z2,z3,z4,z39,z6]),(0,[z1,z2,z3,z4,z444,z7,z6]),(0,[z144,z2,z3,z4,z7,z234,z6]),(0,[z34,z1,z2,z3,z111,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z676]),(0,[z1,z2,z3,z4,z7,z6,z677])],[(0,[z58,z2,z62,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z221,z40]),(0,[z678,z1,z2,z3,z4,z7,z6]),(0,[z1,z3,z4,z112,z7,z68,z6]),(1,[z1,z2,z3,z14,z21,z6])],[(1,[z1,z2,z3,z4,z501,z6]),(0,[z1,z2,z3,z4,z7,z348,z6]),(1,[z1,z67,z3,z4,z68,z6]),(1,[z34,z1,z3,z4,z7,z70])],[(0,[z1,z679,z2,z3,z4,z7,z6]),(0,[z25,z1,z2,z3,z4,z7,z6]),(0,[z680,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z44,z4,z7,z6])],[(0,[z1,z2,z3,z4,z7,z6,z584]),(0,[z1,z2,z3,z4,z7,z681,z6]),(0,[z1,z682,z2,z3,z4,z7,z6]),(0,[z173,z1,z2,z3,z4,z71,z6])],[(0,[z0,z25,z2,z3,z4,z7,z6]),(0,[z0,z1,z2,z3,z4,z158,z6]),(0,[z1,z2,z3,z683,z4,z7,z6]),(0,[z1,z2,z3,z4,z684,z7,z6]),(0,[z1,z2,z3,z685,z4,z7,z6]),(0,[z1,z2,z3,z20,z7,z6,z272]),(0,[z1,z2,z3,z686,z4,z7,z6]),(0,[z1,z26,z2,z3,z4,z7,z70]),(0,[z1,z2,z3,z687,z4,z7,z6]),(1,[z1,z2,z3,z4,z428,z6]),(0,[z1,z2,z3,z4,z7,z6,z688])]],
   [[(0,[z689,z1,z2,z3,z4,z7,z6]),(0,[z1,z690,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z14,z234,z6]),(0,[z92,z1,z2,z3,z4,z21,z6]),(0,[z691,z1,z2,z3,z4,z7,z6])],[(0,[z139,z1,z2,z3,z4,z7,z344]),(0,[z1,z2,z3,z4,z7,z692,z6]),(0,[z693,z1,z2,z3,z4,z7,z6]),(0,[z1,z61,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z193,z20,z7,z6]),(0,[z1,z2,z3,z4,z694,z7,z6])],[(0,[z0,z1,z2,z3,z4,z6,z132]),(0,[z695,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z696,z6])],[(0,[z697,z1,z2,z3,z4,z7,z6]),(0,[z25,z1,z2,z3,z4,z158,z6]),(0,[z1,z2,z3,z4,z14,z90,z6]),(0,[z555,z1,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z698,z7,z6]),(0,[z1,z2,z30,z169,z4,z7,z6]),(1,[z1,z2,z3,z4,z348,z6]),(0,[z1,z2,z699,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z700,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z272]),(1,[z555,z1,z2,z3,z7,z6])],[(0,[z701,z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z702,z3,z4,z7,z6]),(0,[z1,z2,z196,z3,z4,z7,z6])],[(0,[z703,z1,z2,z3,z4,z7,z6]),(0,[z25,z1,z2,z3,z4,z6,z132]),(1,[z1,z2,z3,z4,z6,z584]),(0,[z1,z2,z22,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z6,z704]),(0,[z1,z2,z705,z3,z4,z7,z6])],[(0,[z706,z1,z2,z3,z4,z7,z6]),(0,[z34,z1,z2,z382,z4,z7,z6]),(0,[z64,z1,z2,z22,z4,z7,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z2,z3,z4,z707,z6]),(0,[z58,z120,z62,z3,z4,z6]),(0,[z1,z2,z3,z444,z158,z6]),(0,[z1,z708,z2,z3,z4,z6]),(0,[z1,z2,z3,z709,z7,z6]),(0,[z710,z2,z3,z4,z7,z6])],[(0,[z1,z209,z3,z4,z7,z279]),(0,[z1,z2,z3,z4,z711,z6]),(0,[z1,z2,z3,z4,z598,z6])],[(0,[z1,z2,z3,z4,z712,z6]),(0,[z1,z2,z3,z713,z4,z6]),(0,[z173,z1,z565,z3,z4,z6]),(0,[z94,z2,z3,z4,z21,z6]),(0,[z714,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z31,z50,z6]),(0,[z1,z2,z3,z229,z21,z6]),(0,[z1,z2,z3,z444,z6,z132]),(0,[z1,z2,z3,z53,z491,z6]),(0,[z1,z2,z3,z715,z7,z6]),(0,[z1,z2,z3,z4,z716,z6]),(0,[z1,z2,z3,z717,z7,z6]),(0,[z571,z1,z2,z4,z161,z6]),(0,[z1,z2,z298,z4,z21,z6])],[(0,[z1,z718,z3,z4,z7,z6]),(0,[z1,z2,z4,z7,z6,z719]),(0,[z1,z2,z3,z14,z658,z6]),(0,[z720,z2,z3,z4,z7,z6]),(0,[z721,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z722,z6]),(0,[z1,z2,z3,z4,z723,z6])],[(0,[z1,z2,z3,z4,z7,z724]),(0,[z1,z2,z30,z4,z233,z6]),(1,[z1,z3,z4,z716,z6]),(0,[z1,z2,z3,z7,z725,z272])],[(0,[z208,z1,z2,z223,z4,z6]),(0,[z1,z2,z3,z534,z21,z6]),(0,[z1,z2,z3,z4,z726,z6]),(0,[z1,z2,z3,z4,z727,z6]),(0,[z301,z2,z3,z87,z7,z6]),(0,[z1,z2,z728,z4,z7,z6]),(0,[z1,z2,z3,z4,z729,z6]),(0,[z160,z1,z2,z4,z161,z6])],[(0,[z1,z2,z3,z4,z730,z6]),(0,[z1,z2,z3,z4,z731,z6]),(0,[z1,z2,z3,z732,z21,z6])]],
   [[(0,[z1,z2,z3,z4,z733,z6]),(0,[z1,z2,z3,z87,z734,z6]),(0,[z1,z2,z3,z735,z7,z6]),(0,[z0,z2,z3,z4,z6,z564])],[(0,[z736,z1,z2,z4,z7,z6]),(0,[z269,z203,z3,z4,z14,z6]),(0,[z85,z2,z91,z4,z14,z6]),(0,[z1,z2,z3,z444,z5,z6]),(0,[z1,z2,z490,z4,z14,z6]),(0,[z1,z2,z3,z491,z90,z6]),(0,[z1,z2,z737,z3,z7,z6]),(0,[z1,z2,z3,z445,z14,z6]),(0,[z1,z2,z738,z3,z4,z6])],[(0,[z58,z208,z62,z4,z7,z6]),(0,[z139,z2,z339,z4,z7,z6]),(0,[z144,z2,z3,z76,z21,z6]),(0,[z1,z2,z4,z7,z6,z739]),(0,[z296,z2,z3,z4,z14,z6]),(0,[z1,z2,z488,z3,z14,z6]),(0,[z1,z2,z48,z4,z14,z6])],[(0,[z1,z2,z3,z4,z740,z6]),(0,[z1,z2,z3,z20,z21,z6]),(0,[z1,z3,z20,z42,z21,z6]),(0,[z741,z2,z3,z4,z7,z6]),(0,[z1,z2,z199,z4,z71,z6]),(0,[z1,z2,z3,z4,z97,z742])],[(0,[z1,z2,z3,z4,z743,z6]),(0,[z1,z2,z4,z7,z627,z72]),(0,[z1,z3,z4,z7,z63,z744])],[(0,[z1,z2,z3,z31,z7,z6]),(0,[z181,z2,z3,z76,z21,z6]),(0,[z1,z3,z53,z20,z21,z6])],[(0,[z1,z2,z745,z4,z7,z6]),(0,[z1,z2,z3,z4,z21,z344]),(0,[z1,z2,z3,z4,z746,z6]),(1,[z2,z3,z747,z7,z6]),(0,[z748,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z749,z6]),(0,[z1,z2,z3,z97,z49,z98])],[(0,[z1,z2,z3,z750,z7,z6]),(0,[z1,z2,z3,z751,z7,z6]),(0,[z1,z2,z3,z21,z6,z383])]],
   [[(0,[z1,z2,z128,z3,z21,z6]),(0,[z1,z2,z3,z45,z21,z6]),(0,[z1,z2,z3,z752,z7,z6]),(0,[z1,z2,z3,z4,z753,z6]),(0,[z1,z2,z3,z4,z754,z6]),(0,[z86,z2,z3,z87,z14,z6]),(0,[z755,z1,z2,z3,z4,z6]),(0,[z1,z3,z4,z7,z744,z70]),(0,[z1,z2,z196,z4,z71,z6]),(0,[z1,z2,z756,z4,z21,z6])],[(0,[z269,z517,z3,z4,z7,z6]),(0,[z1,z209,z3,z4,z14,z6]),(0,[z757,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z7,z90,z146]),(0,[z34,z1,z382,z4,z7,z70]),(0,[z1,z177,z2,z3,z100,z6]),(0,[z1,z2,z3,z4,z758,z6]),(0,[z759,z2,z3,z4,z7,z6]),(0,[z16,z1,z17,z3,z21,z6]),(0,[z1,z2,z48,z4,z315,z6]),(0,[z1,z2,z3,z4,z760,z6])],[(0,[z139,z209,z186,z4,z7,z6]),(1,[z2,z761,z4,z7,z6]),(0,[z1,z2,z3,z4,z762,z6]),(0,[z0,z1,z2,z3,z49,z6]),(0,[z1,z2,z36,z37,z7,z6]),(0,[z489,z2,z3,z4,z21,z6])],[(0,[z1,z2,z3,z4,z233,z279]),(0,[z25,z2,z148,z3,z4,z6]),(0,[z1,z2,z3,z763,z7,z6]),(0,[z1,z2,z3,z764,z7,z6]),(0,[z1,z2,z3,z4,z765,z6]),(0,[z96,z1,z2,z4,z14,z72]),(0,[z1,z2,z766,z4,z7,z6]),(0,[z43,z1,z2,z3,z49,z6])],[(0,[z1,z2,z3,z4,z50,z6]),(0,[z1,z2,z3,z134,z4,z6]),(0,[z1,z130,z3,z767,z7,z6]),(0,[z1,z26,z3,z4,z14,z63])],[(0,[z13,z2,z3,z76,z52,z6]),(0,[z1,z768,z3,z4,z7,z6]),(0,[z168,z1,z169,z4,z14,z6]),(0,[z1,z67,z3,z4,z11,z6]),(0,[z1,z2,z3,z567,z21,z6])],[(0,[z1,z2,z3,z4,z769,z6]),(0,[z1,z2,z770,z4,z7,z6]),(0,[z1,z2,z3,z4,z398,z6]),(0,[z296,z2,z3,z4,z349,z6]),(0,[z43,z1,z2,z3,z4,z132])],[(0,[z144,z2,z490,z4,z7,z234]),(0,[z1,z3,z20,z21,z6,z70]),(0,[z1,z2,z3,z4,z771,z6]),(0,[z296,z2,z3,z111,z7,z6]),(0,[z1,z2,z3,z107,z21,z6])]],
   [[(0,[z1,z2,z3,z4,z772,z6]),(0,[z85,z2,z4,z7,z6,z357])],[(0,[z1,z2,z4,z233,z6,z72]),(0,[z1,z2,z3,z444,z14,z6]),(0,[z1,z2,z3,z773,z7,z6]),(0,[z1,z130,z3,z20,z14,z6]),(0,[z1,z2,z3,z4,z219,z6])],[(0,[z1,z2,z223,z3,z774,z6]),(0,[z1,z2,z3,z4,z6,z775]),(0,[z1,z2,z3,z776,z7,z6]),(0,[z1,z2,z3,z4,z777,z6]),(0,[z1,z2,z3,z7,z6,z778]),(0,[z1,z2,z3,z4,z6,z779])],[(0,[z1,z780,z3,z4,z7,z6]),(0,[z1,z2,z781,z4,z7,z6]),(0,[z1,z2,z3,z4,z782,z6]),(0,[z1,z2,z3,z4,z501,z6]),(0,[z1,z3,z767,z4,z7,z6]),(0,[z92,z1,z3,z53,z14,z6]),(0,[z1,z67,z3,z4,z68,z6]),(0,[z1,z783,z3,z4,z7,z6]),(0,[z1,z2,z44,z4,z21,z6])],[(0,[z58,z62,z3,z4,z7,z6]),(0,[z1,z2,z3,z110,z161,z6]),(0,[z1,z2,z3,z4,z784,z21])],[(0,[z1,z785,z3,z4,z7,z6]),(0,[z149,z1,z2,z3,z786,z6])],[(0,[z1,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z787,z6]),(0,[z92,z1,z3,z53,z54,z6]),(0,[z1,z2,z3,z403,z21,z6]),(0,[z1,z67,z3,z4,z716,z6]),(0,[z1,z2,z788,z4,z7,z6])],[(0,[z1,z2,z789,z4,z7,z6]),(0,[z1,z2,z3,z7,z6,z790]),(0,[z791,z1,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z6,z792]),(0,[z1,z8,z3,z4,z68,z6]),(0,[z1,z2,z3,z4,z7,z793]),(0,[z1,z2,z30,z4,z428,z6]),(0,[z16,z489,z2,z3,z7,z272]),(0,[z1,z2,z3,z4,z794,z6])]],
   [[(0,[z208,z1,z2,z4,z7,z6]),(0,[z1,z2,z3,z4,z6,z795]),(0,[z1,z2,z3,z444,z97,z6]),(0,[z1,z2,z3,z14,z664,z6]),(0,[z1,z2,z3,z694,z14,z6]),(0,[z1,z2,z3,z796,z7,z6])],[(0,[z1,z2,z797,z4,z7,z6]),(0,[z1,z2,z3,z4,z798,z6]),(0,[z1,z2,z3,z786,z7,z6])],[(0,[z1,z2,z10,z4,z7,z6]),(0,[z1,z2,z3,z4,z799,z6]),(0,[z1,z3,z4,z7,z6,z800]),(0,[z1,z2,z3,z4,z801,z6]),(1,[z2,z3,z4,z802,z6]),(0,[z1,z2,z3,z32,z21,z6]),(0,[z1,z2,z273,z4,z398,z6]),(0,[z34,z1,z3,z4,z21,z70])],[(0,[z2,z3,z761,z4,z7,z6]),(0,[z555,z1,z2,z3,z7,z6])],[(0,[z1,z2,z3,z4,z233,z344]),(0,[z2,z3,z4,z7,z234,z803]),(0,[z296,z2,z382,z4,z7,z6]),(0,[z1,z2,z804,z37,z7,z6]),(0,[z1,z2,z366,z4,z71,z6])],[(0,[z1,z17,z3,z4,z21,z6])],[(0,[z1,z2,z805,z4,z7,z6]),(0,[z806,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z807,z6,z337]),(0,[z1,z2,z808,z4,z7,z6]),(0,[z1,z387,z48,z4,z7,z6])],[(0,[z1,z2,z3,z809,z7,z6]),(0,[z1,z3,z4,z716,z7,z6]),(0,[z34,z1,z273,z4,z7,z70]),(0,[z1,z2,z3,z161,z49,z6]),(0,[z16,z1,z2,z3,z14,z272])]],
   [[(0,[z1,z2,z3,z4,z810,z6])],[(0,[z1,z2,z3,z4,z811,z6]),(0,[z1,z2,z3,z4,z812,z6])],[(0,[z813,z1,z3,z4,z7,z6]),(0,[z1,z8,z3,z20,z21,z6]),(0,[z814,z2,z3,z4,z7,z6]),(0,[z1,z249,z2,z3,z14,z6])],[(0,[z1,z2,z3,z76,z514,z6]),(0,[z1,z2,z3,z156,z21,z6]),(0,[z1,z2,z3,z28,z7,z6])],[(0,[z1,z2,z3,z815,z7,z6]),(0,[z1,z2,z816,z4,z7,z6]),(0,[z1,z2,z3,z4,z817,z6]),(0,[z1,z2,z36,z37,z141,z6]),(0,[z1,z2,z3,z4,z277,z6])],[(0,[z1,z2,z3,z4,z818,z6]),(0,[z1,z2,z3,z4,z39,z6]),(0,[z1,z2,z3,z588,z21,z6]),(0,[z1,z3,z4,z112,z716,z6]),(0,[z106,z1,z2,z4,z7,z72]),(0,[z1,z2,z3,z4,z97,z192])],[(0,[z1,z2,z3,z4,z819,z6]),(0,[z86,z2,z3,z87,z150,z6]),(0,[z1,z820,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z821,z6]),(0,[z1,z2,z4,z822,z71,z6])],[(0,[z1,z2,z3,z823,z7,z6]),(0,[z1,z2,z3,z4,z98,z140]),(0,[z1,z2,z3,z4,z288,z6])]],
   [[(0,[z1,z2,z824,z4,z7,z6]),(0,[z16,z1,z2,z3,z312,z6])],[(0,[z1,z2,z4,z825,z7,z6]),(0,[z1,z2,z3,z4,z826,z6]),(0,[z1,z2,z3,z476,z21,z6]),(0,[z1,z2,z36,z37,z14,z6]),(0,[z1,z2,z3,z7,z90,z725])],[(0,[z1,z2,z3,z4,z827,z6]),(0,[z1,z2,z3,z638,z21,z6]),(0,[z1,z2,z4,z313,z6,z72]),(0,[z173,z1,z3,z4,z716,z6]),(0,[z1,z2,z3,z112,z49,z6])],[(0,[z13,z2,z3,z76,z7,z6]),(0,[z1,z177,z2,z3,z7,z6])],[(0,[z828,z1,z2,z3,z4,z6]),(0,[z269,z203,z3,z4,z21,z6]),(0,[z1,z2,z3,z118,z50,z6]),(0,[z85,z2,z91,z4,z21,z6]),(0,[z1,z2,z490,z4,z21,z6]),(0,[z346,z1,z3,z4,z7,z70]),(0,[z1,z2,z3,z21,z468,z6]),(0,[z1,z581,z3,z53,z7,z6]),(0,[z1,z2,z196,z4,z822,z6]),(0,[z1,z2,z30,z4,z7,z221]),(0,[z555,z1,z2,z3,z288,z6])],[(0,[z1,z2,z3,z4,z829,z6]),(0,[z1,z177,z3,z20,z7,z6]),(0,[z296,z2,z3,z4,z21,z6]),(0,[z1,z2,z48,z4,z21,z6])],[(0,[z1,z209,z30,z4,z7,z6]),(0,[z1,z2,z3,z107,z786,z6])],[(0,[z830,z2,z3,z4,z7,z6]),(0,[z831,z2,z3,z4,z7,z6]),(0,[z1,z2,z273,z28,z7,z6]),(0,[z1,z2,z3,z4,z7,z744])]],
   [[(0,[z1,z2,z3,z4,z832,z6]),(0,[z1,z2,z3,z4,z141,z6])],[(0,[z1,z2,z3,z4,z833,z6]),(0,[z1,z215,z3,z118,z7,z6]),(0,[z1,z2,z3,z4,z7,z834]),(0,[z1,z2,z3,z4,z835,z6]),(0,[z1,z2,z3,z734,z21,z6]),(0,[z1,z2,z3,z4,z836,z6]),(1,[z1,z3,z4,z7,z744])],[(0,[z1,z2,z3,z4,z837,z6]),(0,[z838,z2,z3,z4,z7,z6]),(0,[z1,z2,z503,z4,z161,z6])],[(0,[z1,z2,z3,z4,z7,z839])],[(0,[z1,z209,z3,z4,z21,z6]),(0,[z85,z2,z761,z4,z7,z6]),(0,[z25,z1,z2,z3,z110,z6]),(0,[z840,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z14,z6]),(0,[z1,z2,z3,z4,z7,z841]),(0,[z1,z2,z116,z3,z4,z6]),(0,[z1,z67,z3,z4,z432,z6])],[(0,[z1,z2,z3,z118,z7,z6]),(0,[z139,z2,z186,z4,z7,z6]),(0,[z1,z2,z3,z110,z112,z6]),(0,[z1,z2,z22,z804,z7,z6]),(0,[z96,z1,z2,z4,z21,z72]),(0,[z1,z2,z3,z4,z14,z793]),(0,[z1,z2,z842,z4,z14,z6])],[(0,[z1,z2,z3,z843,z7,z6]),(0,[z208,z1,z2,z4,z14,z6]),(0,[z1,z2,z490,z4,z7,z72]),(0,[z844,z1,z2,z3,z4,z6]),(0,[z1,z26,z3,z4,z21,z63]),(0,[z1,z2,z4,z428,z6,z72]),(0,[z1,z2,z503,z4,z207,z6]),(0,[z1,z387,z3,z7,z6,z272])]],
   [[(0,[z1,z2,z3,z4,z7,z845]),(0,[z1,z2,z3,z4,z846,z6]),(0,[z847,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z97,z692]),(0,[z168,z1,z169,z4,z21,z6]),(0,[z1,z2,z3,z4,z848,z6]),(0,[z16,z1,z387,z3,z7,z272])],[(0,[z1,z2,z10,z4,z14,z6]),(0,[z1,z2,z3,z524,z21,z6])],[(0,[z1,z2,z3,z4,z849,z6]),(0,[z1,z2,z3,z4,z850,z6]),(0,[z1,z2,z3,z111,z398,z6]),(0,[z555,z1,z2,z3,z14,z6]),(0,[z94,z2,z48,z4,z7,z6]),(1,[z1,z2,z3,z7,z725])],[(0,[z1,z2,z3,z4,z52,z6]),(0,[z144,z2,z3,z4,z7,z803]),(0,[z1,z2,z3,z4,z313,z6]),(0,[z1,z2,z3,z432,z21,z6])],[(0,[z1,z2,z3,z4,z851,z6]),(0,[z1,z852,z3,z4,z7,z6]),(0,[z1,z2,z3,z444,z21,z6]),(0,[z0,z304,z2,z3,z4,z6]),(0,[z1,z130,z3,z20,z21,z6]),(0,[z1,z2,z3,z4,z853,z6]),(0,[z1,z2,z116,z3,z6,z337]),(0,[z64,z1,z2,z22,z7,z6]),(0,[z1,z2,z3,z4,z315,z6])],[(0,[z1,z2,z3,z854,z7,z6]),(0,[z1,z2,z3,z4,z855,z6]),(0,[z1,z2,z3,z4,z7,z856]),(0,[z367,z1,z3,z4,z432,z6])],[(0,[z1,z2,z3,z444,z515,z6]),(0,[z2,z3,z4,z857,z7,z6]),(0,[z92,z1,z3,z53,z21,z6]),(0,[z34,z1,z3,z4,z349,z70]),(0,[z64,z1,z2,z804,z7,z6]),(0,[z1,z2,z3,z7,z6,z725])],[(0,[z1,z2,z3,z4,z858,z6]),(0,[z1,z859,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z803]),(0,[z1,z2,z3,z860,z7,z6]),(0,[z34,z1,z3,z111,z7,z70]),(0,[z1,z2,z3,z861,z7,z6])]],
   [[(0,[z1,z2,z862,z4,z7,z6]),(0,[z43,z1,z2,z3,z4,z373]),(0,[z1,z387,z3,z193,z7,z6])],[(0,[z208,z120,z1,z2,z4,z6]),(0,[z1,z2,z3,z87,z21,z6]),(0,[z25,z2,z3,z444,z158,z6]),(0,[z0,z2,z3,z4,z113,z6]),(0,[z1,z2,z3,z20,z491,z6]),(0,[z1,z2,z3,z4,z863,z6])],[(0,[z0,z682,z2,z3,z4,z6]),(0,[z1,z2,z864,z4,z7,z6]),(0,[z1,z2,z3,z4,z865,z6]),(0,[z1,z2,z3,z28,z14,z6]),(0,[z1,z177,z2,z116,z3,z6]),(0,[z866,z1,z2,z3,z7,z6]),(0,[z1,z867,z3,z4,z7,z6]),(0,[z16,z1,z2,z3,z7,z725])],[(0,[z120,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z868,z7,z6]),(0,[z1,z215,z3,z31,z7,z6]),(0,[z1,z869,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z310,z6]),(0,[z1,z2,z3,z4,z784,z7]),(0,[z1,z3,z4,z21,z6,z870])],[(0,[z1,z2,z3,z4,z871,z6]),(0,[z2,z3,z4,z7,z803,z40])],[(0,[z1,z2,z3,z4,z7,z872]),(0,[z1,z2,z3,z118,z7,z279]),(0,[z873,z1,z2,z3,z4,z6])],[(0,[z0,z1,z2,z3,z110,z6]),(0,[z1,z2,z3,z4,z6,z874]),(0,[z1,z2,z3,z535,z21,z6]),(0,[z160,z1,z2,z4,z668,z6])],[(0,[z1,z2,z3,z4,z875,z6]),(0,[z43,z1,z2,z3,z110,z6]),(0,[z1,z2,z382,z4,z398,z6]),(0,[z1,z2,z3,z4,z876,z6])]],
   [[(0,[z1,z2,z4,z7,z6,z877]),(0,[z878,z1,z2,z3,z7,z6]),(0,[z57,z2,z3,z4,z113,z6]),(0,[z879,z1,z2,z3,z4,z21]),(0,[z1,z2,z3,z288,z21,z6])],[(0,[z1,z880,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z7,z881])],[(0,[z1,z209,z3,z4,z233,z6]),(0,[z1,z215,z3,z4,z50,z6]),(0,[z13,z2,z3,z76,z14,z6]),(0,[z1,z2,z3,z242,z21,z6]),(1,[z1,z2,z804,z7,z6]),(0,[z1,z882,z3,z4,z7,z6]),(0,[z16,z1,z2,z3,z21,z272]),(0,[z489,z2,z48,z4,z7,z6])],[(0,[z1,z2,z883,z3,z7,z6]),(0,[z1,z2,z3,z4,z7,z884]),(0,[z1,z2,z4,z7,z6,z194]),(0,[z1,z2,z3,z812,z7,z6]),(0,[z1,z2,z30,z4,z14,z221])],[(0,[z86,z2,z3,z747,z7,z6]),(0,[z1,z2,z3,z4,z885,z6]),(0,[z1,z2,z3,z4,z886,z6])],[(0,[z58,z852,z3,z4,z7,z6]),(0,[z673,z62,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z887,z6]),(0,[z1,z2,z3,z888,z7,z6]),(0,[z1,z209,z3,z4,z7,z344]),(0,[z173,z1,z3,z4,z42,z6]),(0,[z35,z2,z3,z4,z398,z6]),(0,[z1,z2,z3,z4,z889,z6]),(0,[z594,z1,z2,z3,z4,z132]),(0,[z1,z2,z3,z4,z890,z6])],[(0,[z1,z2,z3,z4,z7,z891]),(0,[z1,z2,z3,z28,z349,z6]),(0,[z1,z2,z3,z4,z892,z6]),(0,[z16,z1,z2,z3,z21,z6])],[(0,[z1,z2,z382,z4,z7,z6]),(0,[z346,z1,z2,z3,z21,z6]),(0,[z1,z2,z3,z4,z893,z6]),(0,[z894,z2,z3,z4,z7,z6])]],
   [[(0,[z1,z2,z3,z895,z7,z6]),(0,[z144,z2,z3,z4,z7,z331]),(0,[z1,z2,z3,z111,z817,z6]),(0,[z1,z2,z196,z4,z65,z6])],[(0,[z1,z2,z896,z4,z7,z6]),(0,[z897,z2,z3,z4,z7,z6]),(0,[z1,z387,z3,z4,z7,z6]),(0,[z1,z3,z28,z7,z6,z70])],[(0,[z1,z2,z898,z4,z7,z6]),(0,[z25,z2,z3,z360,z4,z6]),(0,[z1,z2,z3,z110,z14,z6]),(0,[z1,z2,z3,z4,z899,z6]),(0,[z1,z2,z3,z4,z900,z6]),(0,[z1,z2,z3,z4,z901,z6])],[(0,[z1,z2,z3,z4,z902,z6]),(0,[z1,z2,z3,z4,z150,z6]),(0,[z1,z2,z3,z4,z159,z6]),(0,[z1,z903,z3,z4,z7,z6]),(0,[z759,z2,z3,z4,z21,z6])],[(0,[z1,z215,z3,z4,z7,z6]),(0,[z2,z3,z76,z113,z21,z6]),(0,[z1,z2,z904,z4,z7,z6]),(0,[z168,z1,z905,z4,z7,z6]),(0,[z92,z1,z3,z767,z7,z6]),(0,[z1,z2,z3,z4,z97,z545]),(0,[z1,z906,z3,z4,z7,z6]),(0,[z1,z2,z38,z37,z7,z6]),(0,[z1,z907,z3,z4,z7,z6]),(0,[z1,z2,z908,z4,z7,z6])],[(0,[z35,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z118,z14,z6]),(0,[z1,z2,z3,z4,z909,z6]),(0,[z1,z2,z3,z69,z21,z6]),(0,[z1,z2,z3,z21,z6,z563])],[(0,[z1,z2,z3,z4,z910,z6]),(0,[z139,z2,z186,z118,z7,z6]),(0,[z1,z2,z3,z77,z21,z6]),(0,[z1,z2,z911,z3,z4,z6]),(0,[z16,z94,z2,z3,z7,z272])],[(0,[z1,z2,z912,z4,z7,z6]),(0,[z1,z2,z3,z31,z7,z279]),(0,[z1,z2,z618,z4,z71,z6]),(0,[z1,z2,z3,z4,z913,z6]),(0,[z1,z2,z3,z914,z7,z6]),(0,[z1,z2,z3,z4,z915,z6]),(0,[z1,z2,z3,z114,z7,z90]),(0,[z43,z1,z2,z3,z4,z742])]],
   [[(0,[z1,z2,z3,z916,z7,z6]),(0,[z2,z852,z3,z4,z7,z6]),(0,[z609,z2,z3,z4,z158,z6]),(0,[z1,z2,z3,z4,z917,z6])],[(0,[z1,z2,z3,z4,z918,z6])],[(0,[z1,z2,z3,z4,z7,z919]),(0,[z1,z2,z3,z747,z7,z6]),(0,[z920,z1,z2,z3,z4,z6]),(0,[z921,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z922,z6]),(0,[z1,z2,z3,z4,z923,z6])],[(0,[z924,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z54,z21,z6]),(0,[z1,z2,z382,z28,z7,z6])],[(0,[z1,z2,z925,z4,z7,z6]),(0,[z1,z3,z20,z7,z6,z665]),(0,[z1,z2,z804,z4,z7,z6]),(1,[z489,z2,z3,z21,z6]),(0,[z1,z17,z48,z4,z7,z6])],[(0,[z1,z2,z3,z4,z7,z926]),(0,[z1,z2,z3,z4,z50,z279]),(0,[z1,z2,z761,z4,z7,z6]),(0,[z181,z2,z3,z4,z158,z6]),(0,[z1,z2,z3,z4,z23,z6])],[(0,[z25,z2,z3,z4,z374,z6])]],
   [[(0,[z1,z2,z3,z4,z927,z6]),(0,[z928,z1,z2,z3,z7,z6]),(0,[z1,z2,z3,z7,z6,z337]),(0,[z1,z2,z3,z53,z740,z6]),(0,[z1,z2,z420,z4,z7,z6]),(0,[z1,z929,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z930,z6]),(0,[z931,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z310,z812,z6])],[(0,[z208,z1,z2,z4,z21,z6]),(0,[z1,z2,z62,z3,z774,z6]),(0,[z1,z932,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z734,z6]),(0,[z1,z2,z3,z4,z933,z6]),(0,[z1,z2,z934,z4,z7,z6]),(0,[z35,z2,z3,z28,z7,z6]),(0,[z1,z387,z3,z4,z288,z6])],[(0,[z1,z215,z3,z4,z7,z279]),(0,[z1,z935,z3,z4,z7,z6]),(0,[z2,z3,z87,z76,z21,z6]),(0,[z1,z2,z490,z4,z6,z584]),(0,[z1,z2,z3,z786,z21,z6])],[(0,[z1,z2,z3,z544,z21,z6]),(0,[z2,z3,z747,z4,z7,z6]),(0,[z1,z2,z4,z936,z7,z6])],[(0,[z25,z2,z3,z4,z158,z6]),(0,[z1,z2,z937,z3,z4,z6]),(0,[z1,z2,z273,z4,z7,z6]),(0,[z227,z1,z3,z53,z7,z6]),(1,[z1,z2,z3,z786,z6]),(0,[z16,z489,z2,z3,z21,z6]),(0,[z555,z1,z2,z3,z21,z6])],[(0,[z938,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z939,z6]),(0,[z569,z1,z2,z3,z21,z6]),(0,[z96,z1,z2,z4,z428,z72])],[(0,[z1,z2,z3,z940,z7,z6]),(0,[z1,z2,z3,z31,z14,z6]),(0,[z86,z2,z3,z87,z336,z6]),(0,[z1,z177,z2,z3,z899,z6]),(0,[z1,z2,z3,z624,z21,z6])]],
   [[(0,[z1,z2,z3,z4,z7,z279]),(0,[z1,z2,z3,z31,z7,z344]),(0,[z139,z2,z186,z31,z7,z6]),(0,[z1,z2,z3,z4,z941,z6]),(0,[z1,z2,z3,z558,z21,z6])],[(0,[z1,z2,z3,z942,z7,z6])],[],[(0,[z1,z2,z3,z4,z7,z943]),(0,[z944,z1,z2,z3,z4,z6]),(0,[z1,z130,z387,z3,z7,z6]),(0,[z1,z2,z3,z945,z7,z6])],[(0,[z946,z1,z2,z4,z7,z6]),(0,[z1,z354,z3,z20,z7,z6]),(0,[z509,z1,z2,z4,z472,z6])],[(0,[z1,z2,z4,z7,z6,z947]),(0,[z1,z2,z3,z59,z7,z6]),(0,[z94,z2,z3,z4,z7,z6]),(0,[z948,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z193,z7,z468]),(0,[z1,z2,z3,z28,z21,z6]),(0,[z1,z2,z3,z4,z949,z6])],[(0,[z1,z950,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z802,z6]),(0,[z1,z2,z382,z4,z14,z6]),(0,[z1,z2,z214,z3,z14,z6])],[(0,[z1,z2,z3,z4,z50,z344]),(0,[z139,z2,z186,z4,z50,z6]),(0,[z1,z2,z3,z951,z7,z6]),(0,[z1,z2,z4,z310,z6,z194])]],
   [[(0,[z1,z2,z4,z7,z6,z952]),(0,[z670,z2,z3,z4,z7,z40]),(0,[z610,z1,z2,z3,z21,z6]),(0,[z1,z2,z953,z4,z7,z6]),(0,[z1,z67,z477,z3,z4,z6]),(0,[z680,z1,z2,z3,z4,z132]),(0,[z1,z2,z3,z49,z21,z6]),(0,[z1,z387,z3,z4,z14,z6])],[(0,[z1,z2,z490,z4,z7,z221]),(0,[z1,z2,z3,z4,z7,z954]),(0,[z1,z2,z420,z4,z288,z6])],[(0,[z1,z2,z3,z4,z955,z6])],[(0,[z168,z1,z209,z4,z7,z6]),(0,[z1,z215,z3,z4,z14,z6]),(0,[z1,z2,z196,z622,z4,z6]),(0,[z135,z2,z3,z4,z7,z40]),(0,[z1,z2,z3,z4,z956,z6]),(0,[z1,z3,z767,z20,z7,z6]),(0,[z92,z1,z3,z53,z348,z6])],[(0,[z957,z1,z2,z4,z7,z6]),(0,[z139,z215,z186,z4,z7,z6]),(0,[z25,z2,z3,z4,z802,z6]),(0,[z1,z2,z4,z7,z856,z72])],[(0,[z13,z2,z3,z76,z21,z6]),(0,[z634,z2,z3,z76,z7,z6]),(0,[z958,z1,z2,z3,z4,z6])],[(0,[z58,z10,z62,z4,z7,z6]),(0,[z58,z62,z3,z4,z14,z6]),(0,[z1,z2,z3,z31,z871,z6]),(0,[z2,z761,z186,z4,z7,z6]),(0,[z1,z2,z959,z3,z4,z6]),(0,[z1,z2,z3,z4,z960,z6]),(0,[z86,z2,z3,z87,z21,z6]),(0,[z1,z2,z3,z4,z961,z6]),(0,[z1,z391,z3,z4,z112,z6]),(0,[z1,z2,z4,z822,z7,z6]),(0,[z1,z2,z30,z4,z21,z221]),(0,[z145,z1,z3,z4,z42,z6])],[(0,[z2,z3,z4,z7,z6,z803]),(0,[z1,z3,z905,z4,z7,z6]),(0,[z879,z1,z2,z3,z4,z7]),(0,[z1,z387,z3,z4,z315,z6])]],
   [[(0,[z1,z2,z3,z4,z962,z6]),(0,[z1,z2,z3,z4,z963,z6]),(0,[z1,z2,z3,z150,z21,z6]),(0,[z964,z1,z2,z3,z310,z6]),(0,[z1,z2,z38,z3,z21,z6])],[(0,[z1,z2,z3,z4,z7,z344]),(0,[z2,z3,z4,z965,z7,z6])],[(0,[z1,z2,z3,z966,z4,z6]),(0,[z1,z130,z3,z20,z491,z6]),(0,[z967,z1,z2,z3,z7,z6])],[(0,[z1,z2,z3,z968,z7,z6]),(0,[z120,z1,z2,z10,z4,z6]),(0,[z139,z266,z2,z186,z4,z6]),(0,[z144,z2,z3,z4,z234,z584]),(0,[z1,z2,z3,z4,z54,z6]),(0,[z1,z2,z3,z4,z969,z6]),(0,[z96,z1,z2,z4,z7,z856])],[(0,[z139,z322,z2,z4,z7,z6]),(0,[z1,z2,z3,z47,z21,z6]),(0,[z1,z970,z2,z3,z4,z6]),(0,[z1,z2,z3,z672,z21,z6]),(0,[z1,z2,z387,z3,z21,z6])],[(1,[z1,z2,z3,z774,z6]),(0,[z489,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z110,z21,z6]),(0,[z1,z2,z971,z4,z7,z6]),(0,[z1,z2,z3,z7,z6,z972]),(0,[z1,z2,z3,z4,z312,z6]),(0,[z16,z1,z2,z48,z7,z272])],[(0,[z1,z2,z3,z973,z7,z6]),(0,[z2,z3,z4,z802,z7,z6]),(0,[z43,z1,z2,z3,z4,z520]),(0,[z94,z2,z3,z4,z288,z6])],[(0,[z1,z2,z3,z4,z974,z6]),(0,[z1,z2,z3,z21,z90,z6])]],
   [[(0,[z1,z2,z3,z118,z21,z6]),(0,[z85,z2,z467,z4,z7,z6]),(0,[z1,z2,z4,z6,z194,z584]),(0,[z1,z2,z3,z4,z6,z975]),(0,[z424,z1,z2,z4,z7,z72])],[(0,[z1,z2,z3,z4,z7,z976])],[(0,[z1,z2,z3,z4,z977,z6]),(0,[z1,z2,z3,z119,z21,z6])],[(0,[z1,z2,z3,z978,z4,z6]),(0,[z1,z2,z3,z979,z7,z6]),(0,[z1,z2,z3,z4,z980,z6])],[(0,[z1,z2,z3,z421,z21,z6]),(0,[z1,z981,z3,z4,z7,z6]),(0,[z2,z3,z4,z802,z158,z6]),(0,[z1,z2,z3,z4,z982,z6]),(0,[z1,z2,z3,z4,z349,z6]),(0,[z1,z2,z273,z4,z14,z6]),(0,[z64,z1,z2,z22,z23,z6]),(0,[z1,z2,z3,z4,z983,z6])],[(0,[z1,z2,z3,z4,z984,z6]),(0,[z2,z91,z761,z4,z7,z6]),(0,[z1,z2,z985,z4,z7,z6]),(0,[z1,z2,z3,z105,z21,z6]),(0,[z1,z2,z3,z111,z7,z6]),(0,[z92,z1,z3,z655,z7,z6]),(0,[z34,z1,z3,z4,z398,z70]),(0,[z1,z2,z3,z240,z21,z6])],[(0,[z1,z2,z3,z4,z986,z6]),(0,[z246,z2,z3,z87,z7,z6]),(0,[z144,z2,z3,z4,z7,z234]),(0,[z987,z2,z3,z4,z7,z6]),(0,[z1,z67,z3,z403,z68,z6]),(0,[z16,z1,z387,z3,z21,z6]),(0,[z1,z2,z3,z21,z6,z677]),(0,[z245,z1,z2,z4,z65,z6]),(0,[z1,z2,z420,z4,z315,z6]),(0,[z1,z2,z3,z193,z7,z725])],[(0,[z1,z2,z3,z4,z988,z6]),(0,[z1,z2,z3,z4,z14,z279]),(0,[z1,z2,z3,z521,z21,z6]),(0,[z484,z1,z2,z3,z21,z6]),(0,[z1,z2,z989,z4,z7,z6])]],
   [[(0,[z1,z2,z990,z3,z4,z6]),(0,[z139,z2,z186,z4,z7,z279]),(0,[z1,z2,z3,z76,z39,z6]),(0,[z2,z3,z76,z21,z6,z40]),(0,[z1,z2,z3,z4,z991,z6]),(0,[z1,z2,z3,z4,z992,z6]),(0,[z1,z2,z3,z4,z993,z6])],[(0,[z1,z2,z3,z4,z994,z6]),(0,[z1,z2,z3,z4,z995,z6]),(0,[z1,z2,z3,z4,z7,z996]),(0,[z1,z2,z3,z997,z7,z6]),(0,[z998,z2,z3,z4,z7,z6]),(0,[z1,z2,z30,z4,z7,z109]),(0,[z1,z2,z3,z403,z7,z6]),(0,[z1,z2,z999,z4,z7,z6]),(0,[z1000,z2,z3,z4,z7,z6])],[(0,[z1,z2,z3,z1001,z7,z6]),(0,[z1,z2,z3,z368,z14,z6]),(1,[z1,z2,z4,z7,z856]),(0,[z1,z2,z3,z193,z7,z90]),(0,[z555,z1,z2,z3,z97,z98])],[(0,[z1,z2,z3,z4,z1002,z6]),(0,[z1,z2,z1003,z4,z7,z6]),(0,[z173,z1,z3,z4,z112,z6]),(0,[z1,z2,z4,z71,z6,z608])],[(0,[z1,z2,z30,z31,z7,z6]),(0,[z1,z2,z1004,z3,z4,z6]),(0,[z1,z2,z3,z59,z14,z6]),(0,[z1,z2,z3,z4,z6,z1005]),(0,[z16,z1,z2,z3,z491,z6]),(0,[z1006,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z114,z9]),(0,[z94,z2,z3,z4,z14,z6])],[(0,[z1,z177,z2,z3,z14,z6]),(0,[z1007,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1008,z6]),(0,[z345,z2,z3,z4,z374,z6])],[(0,[z1,z2,z3,z1009,z7,z6]),(0,[z1,z2,z3,z4,z1010,z6]),(0,[z964,z1,z2,z3,z7,z6]),(0,[z1011,z2,z3,z4,z7,z6]),(0,[z1,z3,z4,z7,z6,z744]),(0,[z1,z2,z3,z4,z1012,z6]),(0,[z1,z2,z3,z4,z732,z6]),(0,[z489,z2,z3,z4,z288,z6]),(0,[z16,z1,z2,z420,z7,z272])],[(0,[z1,z2,z3,z1013,z7,z6]),(0,[z1,z2,z3,z4,z1014,z6])]],
   [[(0,[z1,z17,z3,z4,z7,z6]),(0,[z1,z2,z273,z4,z349,z6]),(0,[z16,z1,z2,z3,z21,z90])],[(0,[z1,z2,z1015,z4,z7,z6]),(0,[z1,z2,z273,z111,z7,z6]),(0,[z1,z2,z3,z655,z21,z6])],[(0,[z1,z2,z3,z4,z7,z1016]),(0,[z1,z2,z3,z1017,z7,z6]),(0,[z1,z2,z3,z31,z21,z6]),(0,[z610,z2,z3,z76,z7,z6]),(0,[z25,z2,z3,z4,z466,z6]),(0,[z135,z2,z3,z4,z14,z40])],[(0,[z1,z2,z3,z1018,z7,z6]),(0,[z1,z2,z905,z4,z7,z6]),(0,[z1019,z2,z3,z4,z7,z6]),(0,[z94,z2,z3,z4,z315,z6])],[(0,[z1,z2,z3,z4,z336,z6]),(0,[z1,z2,z3,z4,z1020,z6]),(0,[z1,z2,z3,z1021,z7,z6]),(0,[z1022,z2,z3,z4,z7,z6]),(0,[z1007,z1,z2,z3,z6,z337])],[(0,[z254,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z4,z1023,z6]),(0,[z1,z2,z3,z4,z1024,z6]),(0,[z1,z2,z3,z4,z1025,z6]),(0,[z1,z1026,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z1027,z6]),(0,[z494,z62,z3,z4,z7,z6]),(0,[z1,z2,z3,z118,z233,z6]),(0,[z2,z3,z4,z5,z802,z6]),(0,[z34,z1,z3,z7,z337,z70]),(0,[z1,z2,z3,z14,z380,z6]),(0,[z1,z1028,z3,z4,z7,z6])],[(0,[z1,z2,z3,z53,z312,z6]),(0,[z1,z2,z36,z37,z21,z6]),(0,[z1,z2,z3,z4,z7,z725])]],
   [[(0,[z1,z2,z3,z4,z14,z344]),(0,[z139,z2,z186,z4,z14,z6]),(0,[z1,z2,z4,z7,z6,z1029]),(0,[z1,z2,z3,z1030,z7,z6]),(0,[z1,z2,z3,z4,z1031,z6]),(0,[z296,z2,z3,z4,z398,z6]),(0,[z1,z391,z3,z4,z519,z6]),(0,[z1,z2,z3,z193,z277,z90])],[(0,[z1,z2,z3,z212,z21,z6]),(0,[z1,z2,z3,z118,z7,z344]),(0,[z1,z2,z3,z4,z1032,z6]),(0,[z139,z2,z186,z4,z7,z344])],[(0,[z1033,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1034,z6]),(0,[z1,z2,z3,z21,z280,z6]),(0,[z706,z1,z2,z3,z21,z6]),(0,[z34,z1,z3,z28,z7,z70])],[(0,[z1,z1035,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z1036,z6]),(0,[z1,z2,z3,z110,z519,z6]),(0,[z34,z1,z3,z4,z7,z744]),(0,[z1,z387,z3,z4,z21,z6]),(0,[z1037,z2,z3,z4,z7,z6]),(0,[z1,z387,z420,z4,z7,z6])],[(0,[z1,z2,z1038,z4,z7,z6]),(0,[z1,z2,z1039,z4,z7,z6]),(0,[z489,z2,z3,z4,z14,z6]),(0,[z484,z1,z2,z3,z49,z6])],[(0,[z1,z2,z3,z4,z1040,z6]),(0,[z1,z1041,z3,z4,z7,z6]),(0,[z464,z1,z2,z3,z14,z6]),(0,[z1,z2,z3,z4,z7,z1042]),(0,[z1,z177,z2,z3,z992,z6])],[(0,[z1,z2,z3,z4,z1043,z6]),(0,[z1,z2,z3,z303,z21,z6]),(0,[z1,z215,z3,z4,z21,z6]),(0,[z1,z2,z4,z14,z6,z194]),(0,[z64,z1,z2,z22,z14,z6]),(0,[z1,z2,z908,z4,z21,z6]),(0,[z43,z1,z2,z298,z4,z132])],[(0,[z1,z2,z490,z4,z7,z6]),(0,[z1,z2,z3,z308,z21,z6]),(0,[z1,z2,z1044,z3,z4,z6])]],
   [[(0,[z1045,z2,z3,z4,z7,z6]),(0,[z1,z67,z2,z44,z4,z6]),(0,[z1,z439,z3,z4,z68,z6])],[(0,[z58,z62,z3,z4,z21,z6]),(0,[z1,z2,z3,z1046,z7,z6]),(0,[z266,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z87,z514,z6]),(0,[z1,z2,z3,z114,z21,z90]),(0,[z1,z17,z3,z4,z288,z6])],[(0,[z1,z2,z3,z1047,z4,z6]),(0,[z1,z2,z3,z21,z93,z6]),(0,[z1,z2,z3,z312,z90,z6])],[(0,[z1,z2,z3,z4,z21,z6]),(0,[z1,z2,z3,z4,z7,z1048]),(0,[z1049,z2,z3,z4,z7,z6]),(0,[z1,z136,z3,z20,z7,z6]),(0,[z1,z2,z3,z1050,z7,z6]),(0,[z1,z2,z3,z28,z1051,z6]),(0,[z1,z2,z83,z4,z71,z6]),(0,[z489,z2,z3,z4,z315,z6])],[(0,[z1,z2,z3,z4,z1052,z6]),(0,[z35,z2,z273,z4,z7,z6]),(0,[z1,z2,z3,z111,z14,z6]),(0,[z96,z1,z2,z4,z219,z72]),(0,[z16,z94,z2,z3,z21,z6])],[(0,[z1,z2,z3,z4,z6,z1053]),(0,[z1,z2,z3,z4,z1054,z6]),(0,[z102,z1,z2,z3,z21,z6]),(0,[z144,z2,z3,z4,z14,z234]),(0,[z1,z2,z3,z21,z104,z6])],[(0,[z1,z2,z1055,z3,z7,z6]),(0,[z1,z2,z3,z1056,z7,z6]),(0,[z149,z1,z2,z3,z150,z6]),(0,[z654,z1,z2,z4,z7,z72]),(0,[z1,z2,z3,z4,z1057,z6]),(0,[z1,z2,z3,z4,z1058,z6]),(0,[z1,z2,z3,z4,z1059,z6]),(0,[z1,z2,z3,z4,z1060,z6]),(0,[z1,z177,z387,z3,z7,z6]),(0,[z1,z2,z989,z4,z14,z6])],[(0,[z1,z2,z10,z4,z21,z6]),(0,[z1,z2,z3,z4,z6,z1061]),(0,[z1062,z1,z2,z3,z4,z6]),(0,[z594,z1,z2,z4,z7,z72]),(0,[z1,z2,z3,z1063,z4,z6]),(1,[z1,z2,z3,z4,z742])]],
   [[(0,[z144,z2,z3,z4,z7,z650]),(0,[z1,z2,z3,z31,z233,z6]),(0,[z1,z2,z3,z330,z21,z6]),(0,[z1064,z2,z3,z4,z7,z6]),(0,[z1,z2,z1065,z4,z7,z6]),(0,[z1,z2,z3,z403,z14,z6]),(0,[z1066,z1,z2,z4,z7,z6]),(0,[z160,z1,z2,z4,z472,z6]),(0,[z1,z2,z554,z3,z21,z6]),(0,[z94,z387,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z1067,z6]),(0,[z1,z2,z1068,z4,z7,z6]),(0,[z34,z296,z3,z4,z7,z70]),(0,[z1,z26,z3,z28,z7,z6]),(0,[z96,z1,z2,z4,z7,z72]),(0,[z1,z2,z3,z21,z115,z6]),(0,[z1,z2,z3,z504,z21,z6]),(0,[z1,z2,z3,z193,z14,z90])],[(0,[z139,z2,z134,z186,z4,z6]),(0,[z1,z2,z3,z59,z150,z6]),(0,[z1,z1069,z3,z4,z7,z6]),(0,[z1,z26,z3,z4,z7,z63]),(0,[z1,z2,z3,z21,z6,z317])],[(0,[z1,z2,z808,z4,z21,z6]),(0,[z1,z2,z3,z4,z6,z742])],[(0,[z208,z1,z209,z4,z7,z6]),(0,[z1,z2,z30,z4,z7,z279]),(0,[z1,z130,z3,z20,z501,z6]),(0,[z34,z1,z116,z3,z4,z70])],[(0,[z1,z2,z1070,z4,z7,z6]),(0,[z1,z2,z480,z4,z71,z6]),(0,[z296,z2,z3,z28,z7,z6]),(0,[z1,z2,z3,z4,z1071,z6]),(0,[z599,z1,z2,z3,z21,z6]),(0,[z1,z2,z199,z4,z154,z6])],[(0,[z1,z2,z4,z1072,z7,z6]),(0,[z16,z1,z2,z3,z7,z665]),(0,[z1,z2,z3,z4,z1073,z6]),(0,[z34,z1,z3,z4,z100,z70]),(0,[z1,z2,z4,z936,z21,z6]),(0,[z1,z2,z1074,z4,z7,z6]),(0,[z1,z2,z3,z193,z312,z90])],[(0,[z1,z2,z4,z7,z6,z1075]),(0,[z1,z2,z3,z4,z1076,z6]),(0,[z1,z2,z273,z4,z21,z6]),(0,[z60,z1,z2,z3,z4,z132]),(0,[z1,z3,z4,z7,z6,z870]),(0,[z1,z2,z3,z4,z1077,z6])]],
   [[(0,[z160,z1,z2,z3,z444,z6]),(0,[z173,z1,z3,z4,z586,z6]),(0,[z1,z2,z3,z111,z349,z6])],[(0,[z1,z2,z1078,z3,z4,z6]),(0,[z1,z2,z3,z4,z7,z1079]),(0,[z92,z1,z3,z53,z7,z6]),(0,[z92,z1,z3,z7,z6,z383]),(0,[z1,z2,z1080,z4,z7,z6]),(0,[z1,z2,z3,z4,z1081,z6]),(0,[z1,z2,z298,z4,z7,z6]),(0,[z1,z489,z2,z3,z21,z6])],[(0,[z1,z2,z1082,z4,z7,z6]),(0,[z274,z2,z3,z4,z7,z40]),(0,[z1,z2,z3,z4,z21,z279]),(0,[z1,z2,z3,z1083,z7,z6]),(0,[z1084,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z1085,z6]),(0,[z1,z2,z3,z4,z742,z132])],[(0,[z1,z2,z3,z4,z1086,z6]),(0,[z144,z2,z3,z4,z310,z234]),(0,[z377,z2,z3,z4,z7,z234]),(0,[z1,z2,z3,z4,z1087,z6]),(0,[z1,z2,z3,z4,z1088,z6]),(0,[z92,z1,z387,z3,z7,z6]),(0,[z1,z2,z3,z14,z6,z337]),(0,[z1,z2,z3,z4,z1089,z6])],[(0,[z1,z215,z3,z4,z233,z6]),(0,[z1,z2,z3,z4,z1090,z6]),(0,[z173,z1,z2,z44,z4,z6])],[(0,[z1,z2,z1091,z3,z4,z6]),(0,[z25,z1,z2,z3,z49,z6]),(0,[z1,z2,z3,z4,z1092,z6]),(0,[z1,z2,z3,z4,z1093,z6]),(0,[z1,z2,z3,z740,z21,z6]),(0,[z1,z26,z3,z4,z7,z744]),(0,[z1094,z1,z2,z3,z4,z6]),(0,[z43,z1,z2,z44,z4,z132])],[(0,[z1,z61,z209,z4,z7,z6]),(0,[z1,z2,z1095,z4,z7,z6]),(0,[z1,z17,z3,z4,z315,z6])],[(0,[z1,z2,z3,z4,z1096,z6]),(0,[z1,z215,z3,z4,z7,z344]),(0,[z1,z1097,z3,z4,z7,z6]),(0,[z2,z3,z87,z747,z7,z6]),(0,[z1,z2,z3,z59,z21,z6]),(0,[z431,z2,z3,z4,z5,z6]),(0,[z35,z2,z3,z4,z14,z6]),(0,[z1,z387,z3,z7,z21,z6]),(0,[z94,z2,z420,z4,z7,z6])]],
   [[(0,[z1,z2,z223,z3,z4,z6]),(0,[z1,z2,z3,z1098,z7,z6]),(0,[z1,z61,z702,z4,z7,z6]),(0,[z1,z2,z3,z4,z6,z1099]),(0,[z92,z1,z177,z3,z7,z6]),(0,[z1,z177,z2,z3,z21,z6]),(0,[z1,z2,z4,z7,z6,z856]),(0,[z1,z2,z3,z374,z21,z6]),(0,[z489,z387,z3,z4,z7,z6])],[(0,[z1,z2,z3,z4,z233,z6]),(0,[z1,z2,z378,z4,z161,z6]),(0,[z1,z2,z1100,z3,z7,z6]),(0,[z1,z2,z1101,z4,z7,z6])],[(0,[z1,z2,z3,z4,z1102,z6]),(0,[z1,z209,z4,z7,z6,z72]),(0,[z1,z905,z169,z4,z7,z6])],[(0,[z1,z2,z3,z4,z6,z1103]),(0,[z181,z2,z3,z76,z7,z6]),(0,[z1,z2,z225,z4,z71,z6]),(0,[z16,z1,z17,z3,z7,z272])],[(0,[z1,z2,z3,z4,z1104,z6]),(0,[z25,z2,z3,z59,z158,z6])],[(0,[z58,z223,z62,z3,z4,z6]),(0,[z1,z2,z3,z1105,z7,z6]),(0,[z135,z2,z3,z4,z21,z40]),(0,[z1,z2,z3,z4,z1106,z6]),(0,[z1,z2,z3,z53,z21,z6]),(0,[z1,z2,z3,z4,z1107,z6]),(0,[z1,z2,z382,z4,z349,z6]),(0,[z1,z2,z3,z4,z1108,z6]),(0,[z149,z1,z2,z3,z288,z6]),(0,[z16,z1,z2,z3,z7,z272])],[(0,[z1,z2,z3,z774,z7,z6]),(0,[z1,z2,z3,z1109,z7,z6]),(0,[z1,z2,z756,z4,z7,z6]),(0,[z86,z2,z3,z685,z7,z6]),(0,[z1,z2,z3,z812,z234,z6]),(0,[z1,z2,z3,z4,z7,z1110]),(0,[z346,z1,z2,z3,z7,z272]),(0,[z1,z3,z4,z716,z68,z6]),(0,[z1,z2,z382,z111,z7,z6]),(0,[z1,z2,z3,z4,z1111,z6])],[(0,[z1112,z1,z2,z3,z4,z6]),(0,[z64,z1,z2,z554,z7,z6])]],
   [[(0,[z1,z2,z3,z4,z1113,z6]),(0,[z1,z2,z3,z4,z1114,z6]),(0,[z1,z2,z3,z4,z1115,z6]),(0,[z1,z2,z3,z4,z1116,z6]),(0,[z1,z2,z3,z4,z1117,z6]),(0,[z1,z2,z3,z4,z6,z1118]),(0,[z1,z2,z3,z4,z514,z6]),(0,[z1,z2,z3,z4,z6,z1119])],[(0,[z208,z1,z61,z4,z7,z6]),(0,[z1,z2,z3,z118,z1120,z6]),(0,[z1,z1121,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z1122,z6]),(1,[z1,z387,z3,z21,z6])],[(0,[z1,z2,z30,z4,z313,z6]),(0,[z1,z2,z3,z4,z1123,z6]),(0,[z1,z2,z3,z4,z786,z6]),(0,[z1,z2,z420,z4,z14,z6])],[(0,[z139,z2,z186,z4,z21,z6]),(0,[z1,z2,z3,z4,z1124,z6]),(0,[z1,z2,z3,z87,z39,z6]),(0,[z1,z2,z3,z76,z21,z6]),(0,[z0,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z395,z21,z6]),(0,[z1,z2,z3,z4,z1125,z6]),(0,[z1,z2,z3,z4,z1126,z6]),(0,[z35,z2,z3,z4,z349,z6]),(0,[z1,z2,z3,z4,z1127,z6]),(0,[z1,z2,z3,z4,z1128,z6]),(0,[z2,z3,z4,z965,z21,z6]),(0,[z149,z489,z2,z3,z7,z6])],[(0,[z1,z2,z662,z37,z7,z6]),(0,[z1,z2,z3,z21,z6,z206]),(1,[z1,z2,z3,z812,z6]),(0,[z35,z2,z3,z111,z7,z6]),(0,[z1,z2,z30,z4,z7,z856])],[(0,[z1,z2,z3,z4,z1129,z7]),(0,[z1,z2,z3,z4,z1130,z6]),(0,[z649,z1,z169,z4,z7,z6]),(0,[z1,z2,z3,z4,z1131,z6]),(0,[z1,z2,z3,z49,z68,z6]),(0,[z1,z2,z3,z4,z807,z6])],[(0,[z1,z2,z3,z4,z1132,z6]),(0,[z1,z2,z3,z347,z21,z6])],[(0,[z1,z209,z3,z118,z7,z6]),(0,[z2,z3,z747,z76,z7,z6]),(0,[z1,z2,z3,z402,z21,z6]),(0,[z1133,z2,z3,z4,z7,z6]),(0,[z1,z2,z1134,z3,z4,z6]),(0,[z489,z2,z420,z4,z7,z6])]],
   [[(0,[z1,z2,z3,z404,z21,z6]),(0,[z1,z2,z3,z4,z1135,z6]),(0,[z1,z2,z3,z4,z1136,z6]),(0,[z1137,z2,z3,z4,z7,z6]),(0,[z1138,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z97,z98])],[(0,[z1,z2,z1139,z4,z7,z6]),(0,[z13,z2,z3,z747,z7,z6]),(0,[z0,z2,z3,z4,z802,z6]),(0,[z1,z2,z3,z4,z1140,z6]),(0,[z1,z2,z3,z1141,z7,z6]),(0,[z64,z1,z2,z22,z21,z6]),(0,[z1,z2,z44,z4,z7,z6])],[],[(0,[z1,z2,z3,z1142,z7,z6]),(0,[z1,z2,z3,z4,z1143,z6]),(0,[z1,z2,z3,z4,z523,z132]),(0,[z1,z2,z3,z4,z1144,z6]),(0,[z1145,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z1146,z6]),(0,[z149,z1,z2,z3,z14,z6]),(0,[z16,z1,z2,z48,z21,z6])],[(0,[z1,z67,z2,z3,z444,z6]),(0,[z1,z2,z490,z4,z310,z6]),(0,[z1,z26,z3,z20,z21,z6]),(0,[z1,z2,z1147,z4,z7,z6]),(0,[z1,z2,z3,z4,z1148,z6]),(0,[z1,z2,z30,z4,z7,z260]),(0,[z1,z2,z3,z4,z1149,z6])],[(0,[z1,z2,z3,z7,z6,z1150])],[(0,[z1,z2,z3,z262,z21,z6]),(0,[z1,z2,z3,z4,z1151,z6]),(0,[z1,z2,z1152,z4,z7,z6]),(0,[z149,z1,z2,z3,z54,z6]),(0,[z16,z1,z2,z3,z288,z272])],[(0,[z269,z852,z3,z4,z7,z6]),(0,[z1,z1153,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z1154,z6]),(0,[z1,z2,z3,z4,z1155,z6]),(0,[z1,z2,z1156,z4,z7,z6]),(0,[z1,z2,z3,z111,z21,z6]),(0,[z1,z2,z3,z14,z21,z6]),(0,[z1,z867,z3,z4,z21,z6])]],
   [[(0,[z1,z2,z3,z4,z7,z1157]),(0,[z144,z2,z3,z4,z21,z234]),(0,[z1,z26,z3,z4,z7,z162]),(0,[z34,z1,z3,z4,z7,z70]),(0,[z2,z3,z4,z7,z6,z1158]),(0,[z1,z2,z298,z4,z14,z6])],[(0,[z35,z2,z382,z4,z7,z6]),(0,[z1,z2,z3,z4,z1159,z6]),(0,[z1,z2,z3,z4,z1160,z6]),(0,[z484,z1,z2,z3,z4,z373]),(0,[z1,z2,z3,z4,z1161,z6]),(0,[z1,z2,z3,z4,z98,z742])],[(0,[z1,z2,z3,z110,z68,z6]),(0,[z1,z2,z3,z111,z1060,z6]),(0,[z1,z2,z3,z4,z1162,z6]),(0,[z1,z2,z3,z1163,z7,z6]),(0,[z254,z2,z3,z4,z515,z6]),(0,[z1,z2,z44,z4,z6,z132])],[(0,[z1,z2,z3,z4,z1164,z6]),(0,[z190,z203,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z1165,z6]),(0,[z1,z2,z3,z685,z21,z6]),(0,[z1,z2,z3,z767,z7,z6]),(0,[z1,z2,z3,z4,z428,z6]),(0,[z1,z2,z3,z4,z14,z954])],[(0,[z1,z2,z3,z433,z21,z6]),(0,[z1,z2,z3,z193,z21,z90]),(0,[z1,z2,z842,z4,z7,z6])],[(0,[z1,z2,z1166,z4,z7,z6]),(0,[z1,z2,z3,z4,z1167,z6]),(1,[z1,z3,z767,z7,z6]),(0,[z1,z2,z3,z4,z1168,z6]),(0,[z1,z3,z53,z767,z7,z6])],[(0,[z1,z2,z3,z49,z71,z6])],[(0,[z1,z2,z3,z1169,z7,z6]),(0,[z1,z2,z3,z49,z98,z6])]],
   [[(0,[z1,z2,z3,z1170,z7,z6]),(0,[z1,z2,z3,z4,z1171,z6]),(0,[z1,z2,z3,z4,z348,z6]),(0,[z1,z8,z3,z20,z7,z6]),(0,[z1,z2,z3,z28,z398,z6])],[(0,[z1,z2,z1172,z4,z7,z6]),(0,[z1,z209,z3,z31,z7,z6]),(0,[z139,z2,z186,z4,z233,z6]),(0,[z1,z2,z3,z4,z1173,z6]),(0,[z258,z1,z2,z22,z7,z6]),(0,[z1,z2,z3,z4,z1051,z6]),(0,[z1,z8,z3,z4,z174,z6]),(0,[z60,z1,z2,z3,z21,z90])],[(0,[z1,z2,z3,z4,z774,z6]),(0,[z1,z2,z3,z4,z1174,z6]),(0,[z569,z2,z3,z4,z7,z40]),(0,[z1,z2,z3,z4,z6,z584]),(0,[z1,z2,z3,z4,z1175,z6]),(0,[z1,z17,z420,z4,z7,z6])],[(0,[z1,z2,z3,z4,z1176,z6])],[(0,[z1,z2,z3,z4,z1177,z6]),(0,[z1,z2,z1178,z4,z7,z6]),(0,[z1,z2,z1179,z4,z7,z6]),(0,[z1,z2,z382,z4,z21,z6]),(0,[z181,z2,z3,z4,z284,z6]),(0,[z16,z1,z2,z420,z21,z6]),(0,[z1,z2,z3,z453,z21,z6])],[(0,[z1,z2,z3,z20,z312,z6]),(0,[z1,z2,z3,z4,z1180,z6]),(0,[z60,z1,z2,z3,z4,z253]),(0,[z1,z2,z3,z4,z7,z742])],[(0,[z1,z2,z3,z297,z21,z6]),(0,[z289,z1,z3,z4,z112,z6]),(0,[z1,z2,z3,z28,z1159,z6])],[(0,[z1,z2,z3,z4,z1181,z6]),(0,[z1,z2,z3,z4,z1182,z6]),(0,[z1,z2,z4,z21,z6,z194])]],
   [[(0,[z1,z209,z3,z4,z50,z6]),(0,[z173,z1,z2,z3,z444,z6]),(0,[z34,z35,z3,z4,z7,z70])],[(0,[z1,z2,z3,z4,z491,z6])],[(0,[z269,z203,z3,z4,z7,z6]),(0,[z1,z2,z3,z1183,z7,z6]),(0,[z85,z2,z91,z4,z7,z6]),(0,[z1,z2,z1184,z3,z7,z6]),(0,[z35,z2,z3,z4,z21,z6]),(0,[z1,z2,z4,z161,z822,z6])],[(0,[z1,z2,z3,z1185,z7,z6]),(0,[z296,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z1186,z6]),(0,[z1,z2,z31,z7,z6,z72]),(0,[z1,z2,z3,z311,z21,z6]),(0,[z1,z2,z3,z110,z71,z6]),(0,[z1,z2,z48,z4,z7,z6]),(0,[z489,z2,z3,z7,z21,z6]),(0,[z1,z2,z3,z49,z7,z6]),(0,[z1,z2,z3,z4,z97,z115]),(0,[z16,z1,z2,z3,z315,z272])],[(0,[z852,z62,z3,z4,z7,z6]),(0,[z208,z1,z169,z4,z7,z6]),(0,[z1,z2,z3,z4,z1120,z6]),(0,[z1,z2,z3,z110,z98,z6]),(0,[z149,z1,z387,z3,z7,z6]),(0,[z1,z2,z3,z14,z49,z6])],[(0,[z1,z2,z223,z883,z3,z6]),(0,[z1,z2,z3,z4,z1187,z6]),(0,[z1,z2,z3,z118,z753,z6]),(0,[z1,z2,z3,z4,z1188,z6]),(0,[z1,z2,z3,z7,z6,z1189]),(0,[z1190,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z1191,z7,z6])],[(0,[z1,z1192,z3,z4,z7,z6]),(0,[z1,z2,z1193,z4,z7,z6]),(0,[z64,z1,z2,z22,z514,z6])],[(0,[z135,z2,z3,z4,z7,z803]),(0,[z1,z2,z3,z7,z6,z1194]),(0,[z1,z2,z3,z211,z21,z6]),(0,[z1,z2,z3,z4,z1195,z6]),(0,[z94,z17,z3,z4,z7,z6])]],
   [[(1,[z852,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z1196,z6]),(0,[z1,z2,z3,z4,z1197,z6]),(0,[z1,z2,z3,z333,z21,z6]),(0,[z1,z2,z3,z323,z21,z6]),(0,[z1,z2,z44,z4,z14,z6])],[(0,[z139,z2,z761,z4,z7,z6]),(0,[z86,z2,z3,z87,z7,z6]),(0,[z1,z2,z3,z482,z21,z6])],[(0,[z1,z209,z3,z4,z7,z6]),(0,[z1198,z1,z2,z3,z4,z6]),(0,[z1,z2,z3,z683,z21,z6]),(0,[z1,z2,z3,z4,z1199,z6]),(0,[z1,z2,z3,z4,z822,z6])],[(0,[z203,z852,z3,z4,z7,z6]),(0,[z1,z2,z196,z3,z444,z6]),(1,[z2,z3,z4,z7,z803]),(0,[z1,z2,z3,z4,z1200,z6]),(0,[z1,z2,z1201,z4,z7,z6])],[(0,[z1,z2,z3,z4,z7,z1202]),(0,[z144,z2,z4,z7,z234,z194]),(0,[z1,z2,z3,z4,z114,z98])],[(0,[z1,z1203,z3,z4,z7,z6]),(0,[z1,z2,z3,z31,z727,z6]),(0,[z1,z67,z3,z110,z68,z6]),(0,[z1,z2,z36,z37,z598,z6]),(0,[z1,z2,z420,z4,z21,z6])],[(0,[z168,z1,z169,z4,z7,z6]),(0,[z1,z2,z3,z4,z1204,z6]),(0,[z1,z2,z3,z403,z54,z6]),(0,[z1,z2,z3,z1205,z7,z6]),(0,[z1,z2,z3,z14,z786,z6])],[(0,[z1,z2,z3,z1206,z7,z6]),(0,[z296,z2,z273,z4,z7,z6]),(0,[z34,z1,z3,z4,z14,z70]),(0,[z16,z1,z2,z3,z7,z202]),(0,[z1,z2,z44,z4,z97,z6])]],
   [[(0,[z1,z2,z223,z10,z4,z6]),(0,[z1,z2,z3,z4,z1207,z6]),(0,[z1,z1208,z2,z3,z4,z6]),(0,[z1,z2,z3,z4,z1209,z6]),(0,[z1,z2,z3,z4,z1210,z6]),(0,[z1,z2,z3,z110,z7,z6]),(0,[z1211,z2,z3,z4,z7,z6]),(0,[z1,z2,z30,z4,z7,z264])],[(0,[z1,z2,z3,z4,z7,z1212]),(0,[z1,z2,z490,z4,z7,z279]),(0,[z1,z2,z3,z4,z1213,z6]),(0,[z34,z1,z177,z3,z7,z70]),(0,[z160,z1,z2,z4,z822,z6]),(0,[z1,z2,z3,z4,z1214,z6]),(0,[z1,z2,z3,z4,z493,z115])],[(0,[z1,z2,z3,z4,z1215,z6]),(0,[z1,z2,z3,z444,z7,z6]),(0,[z160,z1,z2,z415,z4,z6]),(0,[z197,z1,z2,z4,z161,z6]),(0,[z2,z3,z4,z7,z6,z1216]),(0,[z1,z130,z3,z20,z7,z6]),(0,[z1,z1217,z2,z3,z4,z6]),(0,[z1,z2,z3,z1218,z7,z6]),(0,[z1,z17,z3,z4,z14,z6])],[(0,[z1,z2,z4,z7,z279,z72]),(0,[z1,z2,z3,z515,z21,z6]),(0,[z1,z67,z530,z3,z4,z6]),(0,[z173,z1,z3,z4,z6,z640]),(0,[z1,z2,z3,z100,z6,z337])],[(0,[z1,z2,z3,z4,z100,z6]),(0,[z1,z1219,z2,z3,z7,z6]),(0,[z1,z2,z3,z21,z6,z337]),(0,[z1,z2,z804,z36,z7,z6]),(1,[z1,z2,z4,z822,z6]),(0,[z1,z2,z3,z21,z6,z495]),(0,[z1,z2,z48,z4,z288,z6])],[(0,[z1,z2,z3,z1220,z7,z6]),(0,[z1,z2,z3,z21,z340,z6]),(0,[z1,z2,z3,z519,z21,z6])],[(0,[z1,z2,z1221,z4,z7,z6]),(0,[z1,z2,z3,z1222,z7,z6]),(0,[z1223,z2,z3,z4,z7,z6]),(0,[z1,z2,z3,z4,z1224,z6]),(0,[z1,z2,z804,z3,z7,z6]),(0,[z1,z2,z3,z4,z1225,z6]),(0,[z1,z2,z4,z7,z221,z856]),(0,[z16,z1,z2,z3,z732,z6])],[(0,[z1226,z1,z2,z3,z4,z7]),(0,[z13,z2,z3,z76,z39,z6]),(0,[z1,z2,z3,z4,z1227,z6]),(0,[z1,z2,z1228,z4,z7,z6]),(0,[z1,z2,z3,z4,z1229,z6]),(0,[z489,z17,z3,z4,z7,z6])]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 8 256 bkB c

def parents : List (ℕ × List W) := expandN 0 (level0 8 rows)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem gf : allGoalFree 0 (level0 8 rows) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pa0 : chunkB SA 2 ((parents.drop 0).take 1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem paend : ((parents.drop 1)).isEmpty = true := by
  decide +kernel

theorem windowsA : windowsG (chunkB SA 2) parents 0 [1] = true :=
  windowsG_cons pa0 (windowsG_nil paend)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 522) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 522).take 524) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1046).take 195) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1241)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [522, 524, 195] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 102).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 102).take 95).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 197).take 59).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [102, 95, 59] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_nil pcend)))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 8) (nb2 := 256) (by norm_num) gf windowsC windowsB windowsA

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem witness_ok : ∀ x : Fin 6 → Bool, Circuit.eval witness (List.ofFn x) = target x := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sample_ok : ∀ k : Fin 256, target (fun i => (rows.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem solve (s : ℕ) (hs : HasCircuitSize 6 target s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = target x := by
  obtain ⟨C, fits, size, computes⟩ := hs
  by_cases hasNot : ∃ g ∈ C.gates, g.op = GateOp.not
  · obtain ⟨g, mem, op⟩ := hasNot
    have short : binaryCost C.gates < C.size :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, mem, by simp [isBinary, op]⟩
    have bound := bound_from_search rows rfl (by decide) reject sample_ok C.gates C.output fits computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witness_ok⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := fits g mem
    change g.op = .and ∨ g.op = .or ∨ g.op = .not at op
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (hasNot ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_37645

theorem PEqualNP.Outside.L_meta_37645 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276813032 * 2 ^ 32 + 4276808864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276813032 * 2 ^ 32 + 4276808864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37645.solve