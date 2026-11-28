import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_39255

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
  Nat.testBit (4277074632 * 2 ^ 32 + 4276156608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x4030d0e321c6c788#64 ++ 0x22018687190e363c#64 ++ 0xc171d3e723cecf97#64 ++ 0xde0b8e9f391e767c#64 : BitVec 256),
   (0x0216220d2c510aac#64 ++ 0x4010b11069628855#64 ++ 0x669e223f3c710fef#64 ++ 0xbb34f111f9e3887f#64 : BitVec 256),
   (0x08e01430402a5150#64 ++ 0x804700a18201528a#64 ++ 0xd8e03c38c07ff1ff#64 ++ 0x76c701e1c603ff8f#64 : BitVec 256),
   (0x17002b409681ac01#64 ++ 0x00b8015a04b40d60#64 ++ 0xdf003fc0ff81fe1e#64 ++ 0xfef801fe07fc0ff0#64 : BitVec 256),
   (0x3ddb4000fb7c001e#64 ++ 0x01eeda0007dbe000#64 ++ 0x3fffc000fffe001d#64 ++ 0xf9fffe0007fff000#64 : BitVec 256),
   (0x9fedbfbe00000000#64 ++ 0x04ff6dfdf0000000#64 ++ 0xbfffffff00000003#64 ++ 0xf5fffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [6, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [3, 9]⟩, ⟨.or, [1, 10]⟩, ⟨.and, [7, 11]⟩, ⟨.or, [8, 12]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [13, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x669e223f3c710fef 0xbb34f111f9e3887f

def z1 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd8e03c38c07ff1ff 0x76c701e1c603ff8f

def z2 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf003fc0ff81fe1e 0xfef801fe07fc0ff0

def z3 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3fffc000fffe001d 0xf9fffe0007fff000

def z4 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc171d3e723cecf97 0xde0b8e9f391e767c

def z5 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbfffffff00000003 0xf5fffffff8000000

def z6 : W := mkw 0x9fffbfbf2c510aac 0x44fffdfdf9628855 0xbfffffff3c000e03 0xfdfffffff9e00070

def z7 : W := mkw 0x8224bfbe00000000 0x041125fdf0000000 0x80003fff00000002 0x040001fff8000000

def z8 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xffffffffc07ff1ff 0xf7fffffffe03ff8f

def z9 : W := mkw 0x0010400021440008 0x00008200010a2000 0x0171c00023ce0015 0xd80b8e00011e7000

def z10 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x271fc3c700000000 0x8138fe1e38000000

def z11 : W := mkw 0x0016000d285002ac 0x4000b00069428015 0x201e000700000000 0x0100f00038000000

def z12 : W := mkw 0x0206220c0c110824 0x4010311060608841 0x260e00001c000000 0x0130700000e00000

def z13 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x7fffe038ffff01ff 0xfbffff01c7fff80f

def z14 : W := mkw 0x0200220004010800 0x0010011000200840 0x460022003c010e0e 0xba30011001e00870

def z15 : W := mkw 0x17162b4dbed1aead 0x40b8b15a6df68d75 0xff9e3ffffff1ffff 0xfffcf1ffffff8fff

def z16 : W := mkw 0x20124001ff7d0abe 0x410092000ffbe855 0x40000000ffff0ffc 0x0a00000007fff87f

def z17 : W := mkw 0x0204220d04010aa0 0x4010211068200855 0x4000223f00010fe2 0x02000111f800087f

def z18 : W := mkw 0x3dc94000d32c0012 0x01ee4a0006996000 0x1961c000c38e0010 0x40cb0e00061c7000

def z19 : W := mkw 0x0000000000000000 0x0000000000000000 0xd8003c00c001f01e 0x76c001e006000f80

def z20 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0xfffffc00fffff01f 0xffffffe007ffff80

def z21 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x269e221f3c310e68 0xa934f110f9e18873

def z22 : W := mkw 0x001200012c510aac 0x4000900009628855 0x000000003c000e00 0x0800000001e00070

def z23 : W := mkw 0x1500000092000000 0x00a8000004900000 0x1f000000ff80001c 0xf8f8000007fc0000

def z24 : W := mkw 0x971fab8f2c510aac 0x44b8fd5c79628855 0x679fe3ff3c710fef 0xbb3cff1ff9e3887f

def z25 : W := mkw 0xd71debcf21c48688 0x26b8ef5e790e2434 0x271fc3c723800e00 0x8938fe1e391c0070

def z26 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080203800000003 0x30040101c0000000

def z27 : W := mkw 0x4020d0e20186c500 0x22010687100c3628 0x8161d1c0038ec010 0x440b0e8e001c7600

def z28 : W := mkw 0x7dfbd0e3fbfec79e 0x23efde871fdff63c 0xffffd3e7fffecf9f 0xfffffe9f3ffff67c

def z29 : W := mkw 0x8ae4bfbe402a5150 0x845725fdf201528a 0xd8e03fffc07ff1ff 0x76c701fffe03ff8f

def z30 : W := mkw 0x4af6f6ff6dffdffc 0xe257b7b7fb6ffeff 0xffffffffffffffff 0xffffffffffffffff

def z31 : W := mkw 0x4010c0c321c6c788 0x22008606190e363c 0x4111c3c723cecf94 0x8a088e1e391e767c

def z32 : W := mkw 0x0000004000808400 0x0000000200040420 0xc10013c02380ce16 0xde08009e011c0670

def z33 : W := mkw 0x17002b0000000000 0x00b8015800000000 0x1e002c0000000000 0x20f0016000000000

def z34 : W := mkw 0x7dfbd0a3fb7e439e 0x23efde851fdbf21c 0x3fffc027fffe019d 0xf9fffe013ffff00c

def z35 : W := mkw 0x0000004000808400 0x0000000200040420 0xd9003fc0e381fe1e 0xfec801fe071c0ff0

def z36 : W := mkw 0x02002b400481ac01 0x0010015a00240d60 0xc0003fc00001fe02 0x060001fe00000ff0

def z37 : W := mkw 0x3fdb6b40fffdac1f 0x01fedb5a07ffed60 0xffffffc0fffffe1f 0xfffffffe07fffff0

def z38 : W := mkw 0x28cb000048380016 0x014658000241c000 0x208e000000300000 0x0104700000018000

def z39 : W := mkw 0x5730fbe3b7c7ef89 0x22b987df1dbe3f7c 0xdf71ffe7ffcfff9f 0xfefb8fff3ffe7ffc

def z40 : W := mkw 0x08e0143000025140 0x804700a18000128a 0xd8e03c380001f1e3 0x76c701e1c0000f8f

def z41 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z42 : W := mkw 0x0204220d04010aa0 0x4010211068200855 0x0000020700000e00 0x0000001038000070

def z43 : W := mkw 0x8224bfbf04010aa0 0x441125fdf8200855 0xc0003fff00010fe2 0x060001fff800087f

def z44 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0x00e00038007e01e1 0x00070001c003f00f

def z45 : W := mkw 0x1fe03f70d6abfd51 0x80ff01fb86b55fea 0xdfe03ff8ffffffff 0xfeff01ffc7ffffff

def z46 : W := mkw 0x28db4000697c001e 0x0146da00034be000 0x38ffc000c07e001d 0x71c7fe000603f000

def z47 : W := mkw 0x002090a200024100 0x0001048510001208 0xc171d3e7004ec197 0xd60b8e9f3802760c

def z48 : W := mkw 0x1de990a200000000 0x00ef4c8510000000 0xbfffd3e700000003 0xf5fffe9f38000000

def z49 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x269e02073c700e0d 0xb934f01039e38070

def z50 : W := mkw 0x08c0041040281050 0x8046002082014082 0x18802c18c0313068 0x20c40160c6018983

def z51 : W := mkw 0x48f0d4f361eed7d8 0xa24786a79b0f76be 0xd9f1ffffe3ffffff 0xfecf8fffff1fffff

def z52 : W := mkw 0x371b6b40bfd5ac0f 0x01b8db5a05fead60 0x271fc3c03f800e00 0x8938fe1e01fc0070

def z53 : W := mkw 0x9724bffe9681ac01 0x04b925fff4b40d60 0xdf003fffff81fe1e 0xfef801fffffc0ff0

def z54 : W := mkw 0x0010400021440008 0x00008200010a2000 0x0111c00023800000 0x88088e00011c0000

def z55 : W := mkw 0x4030506121c6c788 0x22018283090e363c 0xc060102023cecf97 0x5e030081011e767c

def z56 : W := mkw 0x1fc92b0000000000 0x00fe495800000000 0xbfffffc000000003 0xf5fffffe00000000

def z57 : W := mkw 0x17002b0000000000 0x00b8015800000000 0x9f003fc000000002 0xf4f801fe00000000

def z58 : W := mkw 0x88ed94be00000000 0x04476ca5f0000000 0x20ffc03f00000001 0x0107fe01f8000000

def z59 : W := mkw 0x150009409280a401 0x00a8004a04940520 0x010001c003800000 0x0008000e001c0000

def z60 : W := mkw 0x9de99db2402a5150 0x84ef4ced9201528a 0x9961ddc0c00ef010 0x44cb0eee06007780

def z61 : W := mkw 0x9fedbffed6abfd51 0x84ff6dfff6b55fea 0xffffffffffffffff 0xffffffffffffffff

def z62 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xbfffffff007e01e3 0xf5fffffff803f00f

def z63 : W := mkw 0x3dcb0410da381056 0x81ee582086d1c082 0x3e8e2c18dc313068 0x21f47160c6e18983

def z64 : W := mkw 0x4010c0c321c48688 0x22008606190e2434 0x0111c3c723800e00 0x88088e1e391c0070

def z65 : W := mkw 0x4030d0a321464388 0x22018685190a321c 0x0071c027004e0181 0x00038e013802700c

def z66 : W := mkw 0x5730fbe321c6c788 0x22b987df190e363c 0xdf71ffe723cecf97 0xfefb8fff391e767c

def z67 : W := mkw 0x17002b0092000000 0x00b8015804900000 0x9f003fc0ff80001e 0xfcf801fe07fc0000

def z68 : W := mkw 0x150009409280a401 0x00a8004a04940520 0xd9003dc0c381f01e 0x76c801ee061c0f80

def z69 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0x470023c03f810e0e 0xba38011e01fc0870

def z70 : W := mkw 0x3fdf620dff7d0abe 0x41fefb106ffbe855 0x7fffe23fffff0fff 0xfbffff11fffff87f

def z71 : W := mkw 0x0010400121440288 0x00008200090a2014 0x4171c22723ce0f97 0xda0b8e11391e707c

def z72 : W := mkw 0x0200224004818c00 0x0010011200240c60 0xc70033c03f81ce1e 0xfe38019e01fc0e70

def z73 : W := mkw 0x150009409280a401 0x00a8004a04940520 0xd9001fc0e380fe16 0xdec800fe071c07f0

def z74 : W := mkw 0x9fedbfbe40280010 0x04ff6dfdf2014000 0xbfffffffc07e001f 0xf5fffffffe03f000

def z75 : W := mkw 0x02002b0000000000 0x0010015800000000 0x80003fc000000002 0x040001fe00000000

def z76 : W := mkw 0x402090e30082c780 0x220104871804163c 0xc00013e70000cf82 0x0600009f3800067c

def z77 : W := mkw 0xbfffffbefb7c001e 0x05fffffdf7dbe000 0xbffffffffffe001f 0xfdfffffffffff000

def z78 : W := mkw 0x4010c08321440288 0x22008604190a2014 0x0011c00700000000 0x00008e0038000000

def z79 : W := mkw 0x0000000000000000 0x0000000000000000 0x0100000023800014 0xd8080000011c0000

def z80 : W := mkw 0x0010000020400008 0x0000800001020000 0x0010000020400005 0x9800800001020000

def z81 : W := mkw 0x4234f2ef25c7cfa8 0x6211a797792e3e7d 0xc171f3ff23cfcff7 0xde0b8f9ff91e7e7f

def z82 : W := mkw 0x17062b4c9e91ac25 0x40b8315a64f48d61 0xff8e3fd8ffb1fe7e 0xfffc71fec7fd8ff3

def z83 : W := mkw 0x48e0d4f241aed550 0xa24706a7920d76aa 0xd9e1fdf8c3fff1ff 0x76cf0fefc61fff8f

def z84 : W := mkw 0x5720fbe29787ed01 0x22b907df14bc3f68 0xdf61ffc0ff8ffe1e 0xfefb0ffe07fc7ff0

def z85 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x279fe3ff00000003 0xb13cff1ff8000000

def z86 : W := mkw 0xdfedfffe0186c500 0x26ff6ffff00c3628 0xbfffffff038ec013 0xf5fffffff81c7600

def z87 : W := mkw 0x3ddb4001ff7d0abe 0x41eeda000ffbe855 0x7fffc000ffff0ffd 0xfbfffe0007fff87f

def z88 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xd971ffe7e3cfff9f 0xfecb8fff3f1e7ffc

def z89 : W := mkw 0x20124000fb7c001e 0x0100920007dbe000 0x269e0000fffe001d 0xb934f00007fff000

def z90 : W := mkw 0x0020102000024100 0x0001008100001208 0xc0601020004ec197 0x560300810002760c

def z91 : W := mkw 0x9fedbfbe00024100 0x04ff6dfdf0001208 0xffffffff004ec197 0xf7fffffff802760c

def z92 : W := mkw 0x0000000040281050 0x8000000002014082 0x00000000c0313068 0x0000000006018983

def z93 : W := mkw 0x28db4000697c001e 0x0146da00034be000 0x20ffc000007e0001 0x0107fe000003f000

def z94 : W := mkw 0x0000000000000000 0x0000000000000000 0x40802038007101ef 0x32040101c003880f

def z95 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf803ff8fff1ffff 0xfefc01ffc7ff8fff

def z96 : W := mkw 0xbfffffbe697c001e 0x05fffffdf34be000 0xbfffffff007e0003 0xf5fffffff803f000

def z97 : W := mkw 0x68fbd0a3697e439e 0x2347de851b4bf21c 0x20ffc027007e0181 0x0107fe013803f00c

def z98 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc1f1f3ff23ffcfff 0xfe0f8f9ff91ffe7f

def z99 : W := mkw 0x0000000100000280 0x0000000008000014 0x4000022700000f82 0x020000113800007c

def z100 : W := mkw 0x4230fbe325c7ef89 0x221187df192e3f7c 0xc171ffe723cfff97 0xde0b8fff391e7ffc

def z101 : W := mkw 0x17002b0096012801 0x00b8015804b00940 0x1e002c00dc013008 0x20f0016006e00980

def z102 : W := mkw 0x4236f2af2d574bac 0x6211b795796aba5d 0x66ffe23f3c7f0fef 0xbb37ff11f9e3f87f

def z103 : W := mkw 0x88ed94be402a5150 0x84476ca5f201528a 0xf8fffc3fc07ff1ff 0x77c7ffe1fe03ff8f

def z104 : W := mkw 0x48e094f340aad7d0 0xa24704a79a0556be 0xd8e03fffc07fffff 0x76c701fffe03ffff

def z105 : W := mkw 0xbfdf6f1cfb7c001e 0x05fefb78e7dbe000 0x3fffec18fffe001d 0xf9ffff60c7fff000

def z106 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x261e02073c000e00 0x8930f01039e00070

def z107 : W := mkw 0x0af6363d6c7b5bfc 0xc057b1b1eb63dadf 0xfefe3e3ffc7fffff 0xfff7f1f1ffe3ffff

def z108 : W := mkw 0x3de95430d32e5152 0x81ef4aa18699728a 0x9961dc00c38ef010 0x44cb0ee0061c7780

def z109 : W := mkw 0x000000409681ac01 0x0000000204b40d60 0xd8003c00ff81fe1e 0x7ec001e007fc0ff0

def z110 : W := mkw 0x8224bffe0481ac01 0x041125fff0240d60 0xc0003fff0001fe02 0x060001fff8000ff0

def z111 : W := mkw 0x0204220d04010aa0 0x4010211068200855 0x669e223f00010fe3 0xb334f111f800087f

def z112 : W := mkw 0x001200002850000c 0x0000900001428000 0x209e000000700001 0x0104f00000038000

def z113 : W := mkw 0x0204220c00000000 0x0010211060000000 0x269e223f00000003 0xb134f111f8000000

def z114 : W := mkw 0x9de99db200000000 0x04ef4ced90000000 0x9961ddc000000000 0x44cb0eee00000000

def z115 : W := mkw 0x000000409280a401 0x0000000204940520 0x00000000c380f010 0x00000000061c0780

def z116 : W := mkw 0x4020d0e30186c780 0x22010687180c363c 0xc161d3e7038ecf92 0x460b0e9f381c767c

def z117 : W := mkw 0x402090e20082c500 0x2201048710041628 0x800011c00000c000 0x0400008e00000600

def z118 : W := mkw 0x3fdf620cff7d083e 0x41fefb1067fbe841 0x3fffe018ffff007d 0xf9ffff00c7fff803

def z119 : W := mkw 0x00000000402a5150 0x800000000201528a 0x40802038c07ff1ff 0x32040101c603ff8f

def z120 : W := mkw 0x9fcd2f1c96012801 0x04fe6978e4b00940 0x3e8e2c18dc013008 0x21f47160c6e00980

def z121 : W := mkw 0x1de9143000000000 0x00ef48a180000000 0xbffffc3800000003 0xf5ffffe1c0000000

def z122 : W := mkw 0x8224bfbe00025140 0x841125fdf000128a 0xc0003fff0001f1e2 0x060001fff8000f8f

def z123 : W := mkw 0x02002b0004012801 0x0010015800200940 0x00002c0000013000 0x0000016000000980

def z124 : W := mkw 0x3dcb0000da380016 0x01ee580006d1c000 0x3e8e0000dc300008 0x21f4700006e18000

def z125 : W := mkw 0x0004000c00000000 0x0000200060000000 0x209e003f00000001 0x0104f001f8000000

def z126 : W := mkw 0x0020143000025140 0x800100a18000128a 0xc0003c380001f1e2 0x060001e1c0000f8f

def z127 : W := mkw 0x351b4000bb54000e 0x01a8da0005daa000 0x271fc0003f800000 0x8938fe0001fc0000

def z128 : W := mkw 0x7ddbc0c3fbfc869e 0x23eede061fdfe434 0x3fffc3c7fffe0e1d 0xf9fffe1e3ffff070

def z129 : W := mkw 0x0020102000024100 0x0001008100001208 0xd8603c20c04ff19f 0x76c301e106027f8c

def z130 : W := mkw 0x08e01020402a4110 0x0047008102015208 0xd8e01020c07ec19f 0x76c700810603f60c

def z131 : W := mkw 0x20004000d32c0012 0x0100020006996000 0x00000000c38e0010 0x00000000061c7000

def z132 : W := mkw 0x08c0000040280010 0x0046000002014000 0x18e00000c07e001d 0x70c700000603f000

def z133 : W := mkw 0x3ddb4000697c001e 0x01eeda00034be000 0x3fffc000007e0001 0xf1fffe000003f000

def z134 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd8603c38c00ff1f2 0x46c301e1c6007f8f

def z135 : W := mkw 0x08e0143000000000 0x004700a180000000 0x98e03c3800000003 0x74c701e1c0000000

def z136 : W := mkw 0x1ff63f7dfefbfffd 0xc0ffb1fbeff7dfff 0xfffe3fffffffffff 0xfffff1ffffffffff

def z137 : W := mkw 0x9fedbffe9681ac01 0x04ff6dfff4b40d60 0xffffffffff81fe1f 0xfffffffffffc0ff0

def z138 : W := mkw 0x9fffbfbf2c510aac 0x44fffdfdf9628855 0xffffffff3c710fef 0xfffffffff9e3887f

def z139 : W := mkw 0x4010404121c6c788 0x22008202090e363c 0x4010022723cecf97 0x9a008011391e767c

def z140 : W := mkw 0x0236363d2c535bec 0xc011b1b1e9629adf 0xe69e3e3f3c71ffef 0xbf34f1f1f9e38fff

def z141 : W := mkw 0xbfffffbebb54000e 0x05fffffdf5daa000 0xbfffffff3f800003 0xfdfffffff9fc0000

def z142 : W := mkw 0x8224bfbe00000000 0x041125fdf0000000 0x8171ffff00000003 0xd40b8ffff8000000

def z143 : W := mkw 0x1dc9000000000000 0x00ee480000000000 0x3fffc00000000001 0xf1fffe0000000000

def z144 : W := mkw 0x002090a200000000 0x0001048510000000 0x8171d3e700000003 0xd40b8e9f38000000

def z145 : W := mkw 0x0206220c0c110824 0x4010311060608841 0x268e20181c310068 0x21347100c0e18803

def z146 : W := mkw 0x20124000fb7c001e 0x0100920007dbe000 0x00000000fffe001c 0x0800000007fff000

def z147 : W := mkw 0x1ddb00002850000c 0x00eed80001428000 0x3fffc0003c70000d 0xf9fffe0001e38000

def z148 : W := mkw 0x9ded9dbe00000000 0x04ef6cedf0000000 0xb9ffddff00000001 0x45cffeeff8000000

def z149 : W := mkw 0x0000004000808400 0x0000000200040420 0x810011c00380c010 0x4408008e001c0600

def z150 : W := mkw 0x0010000120400288 0x0000800009020014 0x4010022720400f87 0x9a0080113902007c

def z151 : W := mkw 0x3dfb5430fb7e515e 0x81efdaa187dbf28a 0xfffffc38fffff1ff 0xffffffe1c7ffff8f

def z152 : W := mkw 0x0000000000025140 0x800000000000128a 0x400000000001f1e0 0x0200000000000f8f

def z153 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0x40e02038007f01ef 0x32070101c003f80f

def z154 : W := mkw 0x4236f2ef2dd7cfac 0x6211b797796ebe7d 0xe7fff3ff3fffcfff 0xff3fff9ff9fffe7f

def z155 : W := mkw 0x9fe9bff29681ac01 0x04ff4dff94b40d60 0xdf61ffc0ff81fe1e 0xfefb0ffe07fc0ff0

def z156 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x27ffc0003ffe0001 0x893ffe0001fff000

def z157 : W := mkw 0x400000410082c780 0x220000020804163c 0x400000000000cf80 0x020000000000067c

def z158 : W := mkw 0x0ad6220d6c790abc 0x4056b1106b63c855 0x7efe223ffc7f0fff 0xfbf7f111ffe3f87f

def z159 : W := mkw 0x400080c300808680 0x2200040618040434 0x000003c700000e00 0x0000001e38000070

def z160 : W := mkw 0x4010404121c6c788 0x22008202090e363c 0x4000000023cecf94 0x0a000000011e767c

def z161 : W := mkw 0x28f25430fb7e515e 0x814792a187dbf28a 0xd8e03c38fffff1ff 0x7ec701e1c7ffff8f

def z162 : W := mkw 0x9fcd2f1c00000000 0x04fe6978e0000000 0x3e8e2c1800000000 0x21f47160c0000000

def z163 : W := mkw 0xdffdffff21c6c788 0x26ffeffff90e363c 0xffffffff23cecf97 0xfffffffff91e767c

def z164 : W := mkw 0x7ddb4041fbfec79e 0x23eeda020fdff63c 0x7fffc000fffecf9d 0xfbfffe0007fff67c

def z165 : W := mkw 0x9de99db200000000 0x04ef4ced90000000 0xbfffddc000000001 0xf5fffeee00000000

def z166 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0x070003c03f800e00 0x8838001e01fc0070

def z167 : W := mkw 0x0210220124410a88 0x0010811009220854 0x461022273c410f8f 0xba30811139e2087c

def z168 : W := mkw 0x000000409681ac01 0x0000000204b40d60 0x000000003f800e00 0x0800000001fc0070

def z169 : W := mkw 0x402094f30082d7c0 0xa20104a7980416be 0xc0003fff0001ffe2 0x060001fff8000fff

def z170 : W := mkw 0x4030d0e321c48688 0x22018687190e2434 0x8171d3e723800e03 0xdc0b8e9f391c0070

def z171 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x39ffc000c3fe0011 0x41cffe00061ff000

def z172 : W := mkw 0x9fedbfbe00025140 0x84ff6dfdf000128a 0xffffffff0001f1e3 0xf7fffffff8000f8f

def z173 : W := mkw 0x08e01470d6abfd51 0x804700a386b55fea 0xd8e03c38ffffffff 0x7ec701e1c7ffffff

def z174 : W := mkw 0x0ac6261c4c391874 0xc0563130e261c8c3 0x3e8e2c18dc313068 0x21f47160c6e18983

def z175 : W := mkw 0x9fcf2f1c0c110824 0x44fe7978e0608841 0x3e8e2c181c310068 0x21f47160c0e18803

def z176 : W := mkw 0x9fcdaf9e00000000 0x04fe6d7cf0000000 0x3f9fefdf00000000 0xa1fcff7ef8000000

def z177 : W := mkw 0x1dc9000040280010 0x00ee480002014000 0x3fffc000c07e001d 0xf1fffe000603f000

def z178 : W := mkw 0x3ddb4040fffdac1f 0x01eeda0207ffed60 0x7fffc000fffffe1d 0xfbfffe0007fffff0

def z179 : W := mkw 0x8affb6bf2c510aac 0x4457fdb5f9628855 0x66ffe23f3c710fef 0xbb37ff11f9e3887f

def z180 : W := mkw 0x9fffbfbe2850000c 0x04fffdfdf1428000 0xbfffffff3c70000f 0xfdfffffff9e38000

def z181 : W := mkw 0x401240412dd7cfac 0x62009202096ebe7d 0x400000003fffcffc 0x0a00000001fffe7f

def z182 : W := mkw 0x08c9000000000000 0x0046480000000000 0x20ffc00000000001 0x0107fe0000000000

def z183 : W := mkw 0x5710ebc3b7c5ae89 0x22b8875e1dbe2d74 0x0711c3c73f800e00 0x88388e1e39fc0070

def z184 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xd9003fc0c381fe12 0x46c801fe061c0ff0

def z185 : W := mkw 0x001200002850000c 0x0000900001428000 0x269e00003c70000d 0xb934f00001e38000

def z186 : W := mkw 0x9fedbfbf04010aa0 0x44ff6dfdf8200855 0xffffffff00010fe3 0xf7fffffff800087f

def z187 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xc0e03c38007ff1e3 0x060701e1c003ff8f

def z188 : W := mkw 0x48f0d4f361eed7d8 0xa24786a79b0f76be 0xc1f1d3ff23fecff7 0xde0f8e9ff91ff67f

def z189 : W := mkw 0x4030d0a321464388 0x22018685190a321c 0x0171c02723ce0195 0xd80b8e01391e700c

def z190 : W := mkw 0x60124041fbfec79e 0x230092020fdff63c 0x40000000fffecf9c 0x0a00000007fff67c

def z191 : W := mkw 0x4010c0c321c48688 0x22008606190e2434 0x4111c3e723c00f87 0x9a088e1f391e007c

def z192 : W := mkw 0x3fc96b40d7adac13 0x01fe4b5a06bd6d60 0xdf61ffc0ff8ffe1e 0xfefb0ffe07fc7ff0

def z193 : W := mkw 0x1dc9000000000000 0x00ee480000000000 0x1961c00000000000 0x40cb0e0000000000

def z194 : W := mkw 0x3dcb4000db3c0016 0x01ee5a0006d9e000 0x3fefc000dfbe0018 0x61ff7e0006fdf000

def z195 : W := mkw 0x08c0000040280010 0x0046000002014000 0x18800000c0300008 0x20c4000006018000

def z196 : W := mkw 0x000000409681ac01 0x0000000204b40d60 0x40000000ff81fe1c 0x0a00000007fc0ff0

def z197 : W := mkw 0x08d200006878001c 0x004690000343c000 0x3efe0000fc7e001d 0xf9f7f00007e3f000

def z198 : W := mkw 0x17042b4c9681ac01 0x00b8215a64b40d60 0xff9e3fffff81fe1f 0xfffcf1fffffc0ff0

def z199 : W := mkw 0x0214220d20400288 0x0010a11069020014 0x669e223f20400f87 0xbb34f111f902007c

def z200 : W := mkw 0x9de99db200000000 0x04ef4ced90000000 0x99e1fdf800000003 0x74cf0fefc0000000

def z201 : W := mkw 0x1500000092000000 0x00a8000004900000 0x19000000c3800010 0x40c80000061c0000

def z202 : W := mkw 0x751bc0c3bbd4868e 0x23a8de061ddea434 0x271fc3c73f800e00 0x8938fe1e39fc0070

def z203 : W := mkw 0x4032d0e329d6c78c 0x22019687194eb63c 0xe7ffd3e73ffecf9f 0xff3ffe9f39fff67c

def z204 : W := mkw 0x4030d0e221c6c508 0x22018687110e3628 0x8171d1c023cec015 0xdc0b8e8e011e7600

def z205 : W := mkw 0x0000000000000000 0x0000000000000000 0x98003c0000000002 0x74c001e000000000

def z206 : W := mkw 0x02162b4d2cd1aead 0x4010b15a69668d75 0xe69e3fff3c71ffef 0xbf34f1fff9e38fff

def z207 : W := mkw 0x1700220096010800 0x00b8011004b00840 0x5f002200ff810e1e 0xfaf8011007fc0870

def z208 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0xbf1fffc700000002 0xf5f8fffe38000000

def z209 : W := mkw 0x0000808200000000 0x0000040410000000 0x0111c3c700000000 0x80088e1e38000000

def z210 : W := mkw 0x4010404121c48688 0x22008202090e2434 0x0000000023800e00 0x08000000011c0070

def z211 : W := mkw 0x00000000402a5150 0x800000000201528a 0x40000000c07ff1fc 0x020000000603ff8f

def z212 : W := mkw 0x3dcb0000da380016 0x01ee580006d1c000 0x3fffc000dc300009 0xf1fffe0006e18000

def z213 : W := mkw 0x17002b409280a401 0x00b8015a04940520 0x9f003fc0c380f012 0xf4f801fe061c0780

def z214 : W := mkw 0x371f620dbf550aae 0x41b8fb106dfaa855 0x679fe23f3ff10fef 0xbb3cff11f9ff887f

def z215 : W := mkw 0x402090e30082c780 0x220104871804163c 0xc10013e72380cf96 0xde08009f391c067c

def z216 : W := mkw 0x08c00410402a5150 0x804600208201528a 0x58802c18c07ff1fc 0x22c40160c603ff8f

def z217 : W := mkw 0x08f214316c7b5bfc 0xc04790a18b63dadf 0xd8e03c38fc7fffff 0x7ec701e1c7e3ffff

def z218 : W := mkw 0x4036d0ef29d6c7ac 0x6201b687794eb63d 0xe1ffd3ff23fecff7 0xdf0ffe9ff91ff67f

def z219 : W := mkw 0x08f21430687a515c 0x804790a18343d28a 0xfefe3c38fc7ff1ff 0xfff7f1e1c7e3ff8f

def z220 : W := mkw 0x48f0d0e361eec798 0x224786871b0f763c 0xd9f1d3e7e3fecf9f 0xfecf8e9f3f1ff67c

def z221 : W := mkw 0x9fedbfbe04010800 0x04ff6dfdf0200840 0xffffffff3c010e0f 0xfffffffff9e00870

def z222 : W := mkw 0x0236322d2c534bac 0x4011b19169629a5d 0xe6fe323f3c7fcfff 0xff37f191f9e3fe7f

def z223 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xc70013c03f80ce16 0xde38009e01fc0670

def z224 : W := mkw 0xd73dfbef21c6c788 0x26b9efdf790e363c 0xe77fd3e723cecf97 0xdf3bfe9f391e767c

def z225 : W := mkw 0x001240002954000c 0x00009200014aa000 0x27ffc0003ffe001d 0xf93ffe0001fff000

def z226 : W := mkw 0x82042f1c00000000 0x04102178e0000000 0x00002c1800000000 0x00000160c0000000

def z227 : W := mkw 0x0010404021c48408 0x00008202010e2420 0xc171d3c023cece17 0xde0b8e9e011e7670

def z228 : W := mkw 0x0216620d2d550aac 0x4010b310696aa855 0x67ffe23f3fff0fff 0xfb3fff11f9fff87f

def z229 : W := mkw 0x02042b4d0481aea1 0x4010215a68240d75 0xc0003fff0001ffe2 0x060001fff8000fff

def z230 : W := mkw 0x9fcd2f1c40281050 0x84fe6978e2014082 0x3e8e2c18c0313068 0x21f47160c6018983

def z231 : W := mkw 0x4224b2ef0483cfa0 0x6211259778241e7d 0xc00033ff0001cfe2 0x0600019ff8000e7f

def z232 : W := mkw 0x0010400021440008 0x00008200010a2000 0x0000000023ce0014 0x08000000011e7000

def z233 : W := mkw 0x001200012c510aac 0x4000900009628855 0x400000003c710fec 0x0a00000001e3887f

def z234 : W := mkw 0x00000040d6abfd51 0x8000000206b55fea 0x40000000fffffffc 0x0a00000007ffffff

def z235 : W := mkw 0x9509898200000000 0x04a84c4c10000000 0x0101c1c000000000 0x00080e0e00000000

def z236 : W := mkw 0x3dfb5430fb7e515e 0x81efdaa187dbf28a 0xbfffdc00fffef01d 0xfdfffee007fff780

def z237 : W := mkw 0x9fedbfbe96012801 0x04ff6dfdf4b00940 0xbfffffffdc01300b 0xf5fffffffee00980

def z238 : W := mkw 0x4010404121c6c788 0x22008202090e363c 0x4171c00023cecf95 0xda0b8e00011e767c

def z239 : W := mkw 0x4020d0e20186c500 0x22010687100c3628 0xc161d3c0238ece16 0xde0b0e9e011c7670

def z240 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xffffffffc001f01f 0xf7fffffffe000f80

def z241 : W := mkw 0x4010c0c321c48688 0x22008606190e2434 0x0171c3c723ce0e15 0xd80b8e1e391e7070

def z242 : W := mkw 0x9fdf2f1d2c510aac 0x44fef978e9628855 0x7e9e2e3f3c710fef 0xbbf4f171f9e3887f

def z243 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0x8171d3c7238ece10 0xcc0b8e9e391c7670

def z244 : W := mkw 0x08f6143d687a53fc 0xc047b0a1eb43d29f 0xf8fe3c3fc07ff1ff 0x77c7f1e1fe03ff8f

def z245 : W := mkw 0x28fb5430697e515e 0x8147daa1834bf28a 0x20ffc038007e01e1 0x0107fe01c003f00f

def z246 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0x470003c0ff81fe1c 0x8a38001e07fc0ff0

def z247 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0x9f003fc03f800e02 0xfcf801fe01fc0070

def z248 : W := mkw 0x0000004000808400 0x0000000200040420 0xc00013c00000ce02 0x0600009e00000670

def z249 : W := mkw 0x3fdb6b00fb7c001e 0x01fedb5807dbe000 0xbfffffc0fffe001f 0xfdfffffe07fff000

def z250 : W := mkw 0x001200012c510aac 0x4000900009628855 0x408020383c710fef 0x3a040101c1e3887f

def z251 : W := mkw 0x40104041b7c7ef89 0x220082020dbe3f7c 0x40000000ffcfff9c 0x0a00000007fe7ffc

def z252 : W := mkw 0x0016000d285002ac 0x4000b00069428015 0x209e003f007001e1 0x0104f001f803800f

def z253 : W := mkw 0x150009409280a401 0x00a8004a04940520 0x99001dc0c380f010 0x44c800ee061c0780

def z254 : W := mkw 0x08e0143000000000 0x004700a180000000 0xd8e03c38c001f01f 0x76c701e1c6000f80

def z255 : W := mkw 0x1720bbe29681ac01 0x00b905df14b40d60 0xdf71ffe7ff81fe1f 0xfefb8fff3ffc0ff0

def z256 : W := mkw 0x0020143000025140 0x800100a18000128a 0xc0803c380071f1ef 0x360401e1c0038f8f

def z257 : W := mkw 0x02002b400481ac01 0x0010015a00240d60 0xc6003fc03c01fe0e 0xbe3001fe01e00ff0

def z258 : W := mkw 0x0204220c00000000 0x0010211060000000 0x669e223f007101ef 0xb334f111f803880f

def z259 : W := mkw 0x35124000fb7c001e 0x01a8920007dbe000 0x1f000000fffe001c 0xf8f8000007fff000

def z260 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd8803c38c031f1ea 0x26c401e1c6018f8f

def z261 : W := mkw 0x0010000120400288 0x0000800009020014 0x4000000020400f84 0x0a0000000102007c

def z262 : W := mkw 0x0206220c0c110824 0x4010311060608841 0x668e20381c7101ef 0x33347101c0e3880f

def z263 : W := mkw 0xdffdffff21c48688 0x26ffeffff90e2434 0xbfffffff23800e03 0xfdfffffff91c0070

def z264 : W := mkw 0xdffdffbf21464388 0x26ffeffdf90a321c 0xbfffffff004e0183 0xf5fffffff802700c

def z265 : W := mkw 0xbfefbfbeda380016 0x05ff7dfdf6d1c000 0xbfffffffdc30000b 0xf5fffffffee18000

def z266 : W := mkw 0x021222002c51080c 0x0010911001628840 0x669e22003c710e0f 0xbb34f11001e38870

def z267 : W := mkw 0x00000000402a5150 0x800000000201528a 0xd8003c00c07ff1fe 0x76c001e00603ff8f

def z268 : W := mkw 0x0204220c00000000 0x0010211060000000 0x0000223f00000002 0x00000111f8000000

def z269 : W := mkw 0x020022409681ac01 0x0010011204b40d60 0x46002200ff81fe1e 0xba30011007fc0ff0

def z270 : W := mkw 0x0020143000000000 0x000100a180000000 0x80003c3800000002 0x040001e1c0000000

def z271 : W := mkw 0x3fdb6b40fffdac1f 0x01fedb5a07ffed60 0x3fffc3c0fffe0e1d 0xf9fffe1e07fff070

def z272 : W := mkw 0x1de01430d22a5150 0x80ef00a18691528a 0xdfe03c38fffff1ff 0xfeff01e1c7ffff8f

def z273 : W := mkw 0x0216220c2850000c 0x0010b11061428000 0x269e223f3c70000f 0xb934f111f9e38000

def z274 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0x9961ffff00000002 0x44cb0ffff8000000

def z275 : W := mkw 0x5ff0fff3f7efffd9 0xa2ff87ff9fbf7ffe 0xdff1ffffffffffff 0xfeff8fffffffffff

def z276 : W := mkw 0x0204220c04010800 0x0010211060200840 0x669e223f3c010e0f 0xbb34f111f9e00870

def z277 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0x98601c00c00ef010 0x44c300e006007780

def z278 : W := mkw 0x8aedb6be00000000 0x04576db5f0000000 0x26ffe23f00000003 0xb137ff11f8000000

def z279 : W := mkw 0x371f620dbf550aae 0x41b8fb106dfaa855 0x271fc2073f800e00 0x8938fe1039fc0070

def z280 : W := mkw 0x0000000000000000 0x0000000000000000 0x18002c00c0013008 0x20c0016006000980

def z281 : W := mkw 0x3ffb7f70fffffd5f 0x81ffdbfb87ffffea 0xfffffff8ffffffff 0xffffffffc7ffffff

def z282 : W := mkw 0x9fffbfbf6c7b5bfc 0xc4fffdfdfb63dadf 0xfffffffffc7fffff 0xffffffffffe3ffff

def z283 : W := mkw 0xddf9ddf321c6c788 0x26efceef990e363c 0xd971dfe723cecf97 0xdecb8eff391e767c

def z284 : W := mkw 0x0204220d04010aa0 0x4010211068200855 0x4080223f00710fef 0x32040111f803887f

def z285 : W := mkw 0x0000000000000000 0x0000000000000000 0x400020000001000e 0x3200010000000800

def z286 : W := mkw 0x000000400481ac01 0x0000000200240d60 0x400000000001fe00 0x0200000000000ff0

def z287 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xbfffffffc00ef013 0xf5fffffffe007780

def z288 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xc0e01038007ec1f7 0x56070081c003f60f

def z289 : W := mkw 0x9fcd2f1c00000000 0x04fe6978e0000000 0x3fffec1800000001 0xf1ffff60c0000000

def z290 : W := mkw 0x0ae6363c4c3b5974 0xc05731b1e261dacb 0xfeee3c38dc7ff1ff 0x77f771e1c6e3ff8f

def z291 : W := mkw 0x7dfbd4f3fbfed7de 0xa3efdea79fdff6be 0xffffffffffffffff 0xffffffffffffffff

def z292 : W := mkw 0x28d24000fb7c001e 0x0146920007dbe000 0x18e00000fffe001d 0x78c7000007fff000

def z293 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3e8e0000fffe001c 0x29f4700007fff000

def z294 : W := mkw 0x17002b0096012801 0x00b8015804b00940 0x9f003fc0dc01300a 0xf4f801fe06e00980

def z295 : W := mkw 0x08c0000040280010 0x0046000002014000 0x18600000c00e0010 0x40c3000006007000

def z296 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x661e223f3c010fe2 0x8b30f111f9e0087f

def z297 : W := mkw 0x0216224dbed1aead 0x4010b1126df68d75 0x669e223ffff1ffff 0xbb34f111ffff8fff

def z298 : W := mkw 0x0000000000000000 0x0000000000000000 0x0171c00000000001 0xd00b8e0000000000

def z299 : W := mkw 0x972dbbae00000000 0x04b96ddd70000000 0xa77fd3e700000003 0xd53bfe9f38000000

def z300 : W := mkw 0xbfdfeb8efb7c001e 0x05feff5c77dbe000 0x3fffc3c7fffe001d 0xf9fffe1e3ffff000

def z301 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0x98e03c38007e01e3 0x74c701e1c003f00f

def z302 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000007101ec 0x020000000003880f

def z303 : W := mkw 0x002090e200808400 0x0001048710040420 0xc171d3e72380ce17 0xde0b8e9f391c0670

def z304 : W := mkw 0x17162b4dbed1aead 0x40b8b15a6df68d75 0x271e03c73f800e00 0x8938f01e39fc0070

def z305 : W := mkw 0x3dfb5430fb7e515e 0x81efdaa187dbf28a 0x3fffc038fffe01fd 0xf9fffe01c7fff00f

def z306 : W := mkw 0x0000000096012801 0x0000000004b00940 0x00000000dc013008 0x0000000006e00980

def z307 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xffffffff007101ef 0xf7fffffff803880f

def z308 : W := mkw 0x3dc94000d32c0012 0x01ee4a0006996000 0x1f61c000ff8e001c 0xf8fb0e0007fc7000

def z309 : W := mkw 0x9ffdffbe21440008 0x04ffeffdf10a2000 0xbfffffff23ce0017 0xfdfffffff91e7000

def z310 : W := mkw 0x80209db200000000 0x040104ed90000000 0x80001dc000000000 0x040000ee00000000

def z311 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbfeffdd800000000 0x65ff7feec0000000

def z312 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0x27ffc3ff00000001 0x813ffe1ff8000000

def z313 : W := mkw 0x00000000402a5150 0x800000000201528a 0x00000000007e01e0 0x000000000003f00f

def z314 : W := mkw 0x17203b609683ed01 0x00b901db04b41f68 0xdf603fe0ffcfff9f 0xfefb01ff07fe7ffc

def z315 : W := mkw 0x0016000d2c510aac 0x4000b00069628855 0x609e003f3c710fed 0x0b04f001f9e3887f

def z316 : W := mkw 0x000009400080a401 0x0000004a00040520 0x80001dc00000f000 0x040000ee00000780

def z317 : W := mkw 0xdffdffffb7c7ef89 0x26ffeffffdbe3f7c 0xffffffffffcfff9f 0xfffffffffffe7ffc

def z318 : W := mkw 0x001200012850028c 0x0000900009428014 0x669e02273c700f8f 0xbb34f01139e3807c

def z319 : W := mkw 0x08e0143040281050 0x804700a182014082 0x98e03c38c031306b 0x74c701e1c6018983

def z320 : W := mkw 0x3ddb4001fb7c029e 0x01eeda000fdbe014 0x7fffc227fffe0f9f 0xfbfffe113ffff07c

def z321 : W := mkw 0x17002b0000000000 0x00b8015800000000 0x070003c000000000 0x8038001e00000000

def z322 : W := mkw 0x20124000bb54000e 0x0100920005daa000 0x000000003f800000 0x0800000001fc0000

def z323 : W := mkw 0x0216220d285002ac 0x4010b11069428015 0x269e223f007001e3 0xb134f111f803800f

def z324 : W := mkw 0x0020143000025140 0x800100a18000128a 0xc0603c38004ff1f7 0x560301e1c0027f8f

def z325 : W := mkw 0x4030d0e3b7c7ef89 0x220186871dbe3f7c 0xc171d3e7ffcfff9f 0xde0b8e9f3ffe7ffc

def z326 : W := mkw 0x00201430402a5150 0x800100a18201528a 0xc0003c38c07ff1fe 0x060001e1c603ff8f

def z327 : W := mkw 0x08c0000040280010 0x0046000002014000 0x00e00000007e0001 0x000700000003f000

def z328 : W := mkw 0xbdffd4befb7c001e 0x05effea5f7dbe000 0x3fffc03ffffe001d 0xf9fffe01fffff000

def z329 : W := mkw 0x17002b0096012801 0x00b8015804b00940 0x1f002c00ff81301c 0xf8f8016007fc0980

def z330 : W := mkw 0x9de99db200000000 0x04ef4ced90000000 0x9971dfe700000003 0xd4cb8eff38000000

def z331 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd8601c00c07ff1fc 0x46c300e00603ff8f

def z332 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3f7fc000ff8e0010 0xc9fbfe0007fc7000

def z333 : W := mkw 0x0000000004010800 0x0000000000200840 0x400000003c010e0c 0x0a00000001e00870

def z334 : W := mkw 0x0224b2ae00000000 0x0011259570000000 0xa7fff3ff00000003 0xf53fff9ff8000000

def z335 : W := mkw 0x9fcd2f1c00000000 0x04fe6978e0000000 0x3e9e2e3f00000003 0xb1f4f171f8000000

def z336 : W := mkw 0x0204220c04010820 0x4010211060200841 0x0000201800010060 0x00000100c0000803

def z337 : W := mkw 0x9fefbfbe0c110824 0x44ff7dfdf0608841 0xbfffffff1c31006b 0xf5fffffff8e18803

def z338 : W := mkw 0x08c0041040281050 0x8046002082014082 0x0080001800300060 0x00040000c0018003

def z339 : W := mkw 0x0af6363d2c510aac 0x4057b1b1e9628855 0xfefe3e3f3c710fef 0xfff7f1f1f9e3887f

def z340 : W := mkw 0x001200012c510aac 0x4000900009628855 0x401002273c710fef 0x9a00801139e3887f

def z341 : W := mkw 0x9fedbfbe92000000 0x04ff6dfdf4900000 0xbfffffffff80001f 0xfdfffffffffc0000

def z342 : W := mkw 0x2adf620d6d7d0abe 0x4156fb106b6be855 0x66ffe23f3c7f0fef 0xbb37ff11f9e3f87f

def z343 : W := mkw 0x0200220000000000 0x0010011000000000 0x0600220000000002 0xb030011000000000

def z344 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0x98e03c18c03ff078 0x64c701e0c601ff83

def z345 : W := mkw 0x0000000000000000 0x0000000000000000 0x0080201800310068 0x20040100c0018803

def z346 : W := mkw 0x1de01d70d2aaf551 0x80ef00eb869557aa 0xd9e03df8c3fff1ff 0x76cf01efc61fff8f

def z347 : W := mkw 0x1fe03f70d6abfd51 0x80ff01fb86b55fea 0xdf603fc0ff8ffe1e 0xfefb01fe07fc7ff0

def z348 : W := mkw 0x402090e30082c780 0x220104871804163c 0xc171d3e70000cf83 0xd60b8e9f3800067c

def z349 : W := mkw 0x002010600082c500 0x0001008300041628 0xc16013e023cecf97 0xde0b009f011e767c

def z350 : W := mkw 0x9fcdab8e00000000 0x04fe6d5c70000000 0x3fffc3c700000001 0xf1fffe1e38000000

def z351 : W := mkw 0x17002b40d6abfd51 0x80b8015a06b55fea 0xdf003fc0fffffffe 0xfef801fe07ffffff

def z352 : W := mkw 0x0000004000808400 0x0000000200040420 0x400000002380ce14 0x0a000000011c0670

def z353 : W := mkw 0x0016000d285002ac 0x4000b00069428015 0x609e023f20700fe7 0x9b04f011f903807f

def z354 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbe8e3fff00000002 0x25f471fff8000000

def z355 : W := mkw 0x08f01431606a53d8 0x804780a18b03529e 0xd8f03e3fe07fffff 0xfec781f1ff03ffff

def z356 : W := mkw 0x48f0d4b3616e53d8 0xa24786a59b0b729e 0xd8f1fc3fc07ff1ff 0x76c78fe1fe03ff8f

def z357 : W := mkw 0xbfffffbefb7e515e 0x85fffffdf7dbf28a 0xfffffffffffff1ff 0xffffffffffffff8f

def z358 : W := mkw 0x17162b0dbe512aad 0x40b8b1586df28955 0x7e9e2e3ffc713fef 0xbbf4f171ffe389ff

def z359 : W := mkw 0x0030d0a221440008 0x00018685110a2000 0x8171d3e723ce0017 0xdc0b8e9f391e7000

def z360 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0x8171d1e703cec191 0x440b8e8f381e760c

def z361 : W := mkw 0x4032d0e32dd7cfac 0x62019687196ebe7d 0xc171d3e73fffcfff 0xde0b8e9f39fffe7f

def z362 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x269e023f3c700fe1 0x8934f011f9e3807f

def z363 : W := mkw 0x1dc00000d2280010 0x00ee000006914000 0x1fe00000fffe001d 0xf8ff000007fff000

def z364 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0x9f001fc0ff80fe10 0xccf800fe07fc07f0

def z365 : W := mkw 0x001200002850000c 0x0000900001428000 0x261e00003c000000 0x8930f00001e00000

def z366 : W := mkw 0xbfffffbfff7d0abe 0x45fffffdfffbe855 0xffffffffffff0fff 0xfffffffffffff87f

def z367 : W := mkw 0x1500004092808400 0x00a8000204940420 0xdf0013c0ff80ce1e 0xfef8009e07fc0670

def z368 : W := mkw 0x4216624d2dd7cfac 0x6210b312696ebe7d 0x669e223f3fffcfff 0xbb34f111f9fffe7f

def z369 : W := mkw 0x0020102000024100 0x0001008100001208 0x80601000000ec010 0x4403008000007600

def z370 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000020020000e06 0x9a00001001000070

def z371 : W := mkw 0x351b4000bb54000e 0x01a8da0005daa000 0x277fc0003fce0015 0xd93bfe0001fe7000

def z372 : W := mkw 0x3fdf620dff7d0abe 0x41fefb106ffbe855 0x3fffc207fffe0e1d 0xf9fffe103ffff070

def z373 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0x0171c3e723ce0f81 0x880b8e1f391e707c

def z374 : W := mkw 0x0000000092000000 0x0000000004900000 0x00000000ff80001c 0x0800000007fc0000

def z375 : W := mkw 0x0216224d2cd18eac 0x4010b11269668c75 0xe79e33ff3ff1cfff 0xff3cf19ff9ff8e7f

def z376 : W := mkw 0x0000000104010aa0 0x4000000008200855 0x4000000000010fe0 0x020000000000087f

def z377 : W := mkw 0x3fff763dff7f5bfe 0xc1fffbb1effbfadf 0xfffffe3fffffffff 0xfffffff1ffffffff

def z378 : W := mkw 0x17102b41b6c1ae89 0x00b8815a0db60d74 0xdf103fe7ffc1ff9f 0xfef881ff3ffe0ffc

def z379 : W := mkw 0x4010c0c321c48688 0x22008606190e2434 0xc111d3c72380ce16 0xde088e9e391c0670

def z380 : W := mkw 0x4030d0a321464388 0x22018685190a321c 0xc071d027004ec197 0x56038e813802760c

def z381 : W := mkw 0x3ddb4410fb7c105e 0x81eeda2087dbe082 0x3fffec18ffff307d 0xf9ffff60c7fff983

def z382 : W := mkw 0x002090a200000000 0x0001048510000000 0x800013e700000002 0x0400009f38000000

def z383 : W := mkw 0x0004000d000002a0 0x4000200068000015 0x0000003f000001e0 0x00000001f800000f

def z384 : W := mkw 0x4010400121464388 0x22008200090a321c 0x00000000004e0180 0x000000000002700c

def z385 : W := mkw 0x0200220004010800 0x0010011000200840 0x060002003c000e00 0x8830001001e00070

def z386 : W := mkw 0x0010000120400288 0x0000800009020014 0x0010020720000e00 0x8800801039000070

def z387 : W := mkw 0x3dd94000f36c001a 0x01eeca00079b6000 0x1971c000e3ce0015 0xd8cb8e00071e7000

def z388 : W := mkw 0x971fab8f2c510aac 0x44b8fd5c79628855 0x271fc3c73c000e00 0x8938fe1e39e00070

def z389 : W := mkw 0x88ed94be402a5150 0x84476ca5f201528a 0x20ffc03f007e01e1 0x0107fe01f803f00f

def z390 : W := mkw 0x20124040fffdac1f 0x0100920207ffed60 0x40000000fffffe1c 0x0a00000007fffff0

def z391 : W := mkw 0x0206220c0c110824 0x4010311060608841 0x269e223f1c31006b 0xb134f111f8e18803

def z392 : W := mkw 0x003090a320400288 0x0001848519020014 0xc171d3e720400f87 0xde0b8e9f3902007c

def z393 : W := mkw 0x1fc02f10d6293851 0x80fe017886b149c2 0x1e802c18dc313068 0x20f40160c6e18983

def z394 : W := mkw 0x351b4000bb54000e 0x01a8da0005daa000 0x3f1fc000ff80001c 0xf9f8fe0007fc0000

def z395 : W := mkw 0x1509000000000000 0x00a8480000000000 0x271fc00000000000 0x8138fe0000000000

def z396 : W := mkw 0x9724bfbe00000000 0x04b925fdf0000000 0x9f003fff00000002 0xf4f801fff8000000

def z397 : W := mkw 0x4220bbe30483ef81 0x221105df18241f7c 0xc0003fe70001ff82 0x060001ff38000ffc

def z398 : W := mkw 0x1720bba200000000 0x00b905dd10000000 0x9f71ffe700000003 0xf4fb8fff38000000

def z399 : W := mkw 0x28df400d697c02be 0x4146fa006b4be015 0x20ffc03f007e01e1 0x0107fe01f803f00f

def z400 : W := mkw 0x0ae03630442b5950 0x805701b182215aca 0xdee03e38fc7fffff 0xfef701f1c7e3ffff

def z401 : W := mkw 0x17106b40b7c5ac09 0x00b8835a05be2d60 0xdf71ffc0ffcffe1f 0xfefb8ffe07fe7ff0

def z402 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbf7fdfc700000000 0xc5fbfefe38000000

def z403 : W := mkw 0x0000000000000000 0x0000000000000000 0x98001c00c000f010 0x44c000e006000780

def z404 : W := mkw 0x0000000000000000 0x0000000000000000 0x269e000000000001 0xb134f00000000000

def z405 : W := mkw 0x02002b400481ac01 0x0010015a00240d60 0x000003c000000e00 0x0000001e00000070

def z406 : W := mkw 0x0000000000000000 0x0000000000000000 0xc00010000000c016 0x5600008000000600

def z407 : W := mkw 0x350b00009a100006 0x01a8580004d08000 0x260e00001c000000 0x0130700000e00000

def z408 : W := mkw 0x0204220c00000000 0x0010211060000000 0x261e020700000000 0x8130f01038000000

def z409 : W := mkw 0x0000400001040000 0x0000020000082000 0x0161c000038e0010 0x400b0e00001c7000

def z410 : W := mkw 0x4030d0e361eed7d8 0xa20186871b0f76be 0xc171d3e7e3ffffff 0xde0b8e9f3f1fffff

def z411 : W := mkw 0x970dabce9681ac01 0x04b86d5e74b40d60 0xff1fffc7ff81fe1e 0xfff8fffe3ffc0ff0

def z412 : W := mkw 0x0010400021440008 0x00008200010a2000 0x0071c000004e0001 0x00038e0000027000

def z413 : W := mkw 0x68fbd0e369fec79e 0x2347de871b4ff63c 0xe1ffd3e723fecf97 0xdf0ffe9f391ff67c

def z414 : W := mkw 0x88ed94be00000000 0x04476ca5f0000000 0xa1ffd3ff00000003 0xd50ffe9ff8000000

def z415 : W := mkw 0x08c0041040281050 0x8046002082014082 0x58802c38c07131ef 0x32c40161c603898f

def z416 : W := mkw 0x08e0143000024100 0x004700a180001208 0xd8e03c38004ec197 0x76c701e1c002760c

def z417 : W := mkw 0x9fed3f3c00000000 0x04ff69f9e0000000 0xbeee3c3800000003 0x75f771e1c0000000

def z418 : W := mkw 0x3fcb2b00de392817 0x01fe595806f1c940 0x3e8e2c00dc313008 0x21f4716006e18980

def z419 : W := mkw 0x3dc90000d2280012 0x01ee480006914000 0x18000000c0000000 0x00c0000006000000

def z420 : W := mkw 0x400040400186c500 0x22000202000c3628 0x00000000038ec010 0x00000000001c7600

def z421 : W := mkw 0x48e0d4f241aed550 0xa24706a7920d76aa 0x9961ddc0c38ef010 0x44cb0eee061c7780

def z422 : W := mkw 0x0000000000000000 0x0000000000000000 0x00600000004e0015 0x5003000000027000

def z423 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0x4071c02723cecf95 0x0a038e01391e767c

def z424 : W := mkw 0x37126b40fffdac1f 0x01b8935a07ffed60 0xdf003fc0fffffe1e 0xfef801fe07fffff0

def z425 : W := mkw 0x351b4000bb54000e 0x01a8da0005daa000 0x279fc0003ff0000d 0xb93cfe0001ff8000

def z426 : W := mkw 0x4030d0a321464388 0x22018685190a321c 0x4071c227204e0f87 0x9a038e113902707c

def z427 : W := mkw 0x0000000040280010 0x0000000002014000 0x00000000c07e001c 0x000000000603f000

def z428 : W := mkw 0x0ae4363c402a5150 0x805721b1e201528a 0xfefe3e3fc07ff1ff 0xf7f7f1f1fe03ff8f

def z429 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x4000223f3c710fee 0x0a000111f9e3887f

def z430 : W := mkw 0xa8ffd4be697c001e 0x0547fea5f34be000 0x20ffc03f007e0001 0x0107fe01f803f000

def z431 : W := mkw 0x08e094b2402a5150 0x804704a59201528a 0xd9f1ffffc07ff1ff 0xf6cf8ffffe03ff8f

def z432 : W := mkw 0x3dfbd0a2fb7c001e 0x01efde8517dbe000 0xbfffd3e7fffe001f 0xfdfffe9f3ffff000

def z433 : W := mkw 0x9fcd2f5c9681ac01 0x04fe697ae4b40d60 0xff8e3fd8ff81fe1e 0xfffc71fec7fc0ff0

def z434 : W := mkw 0x2216620dff7d0abe 0x4110b3106ffbe855 0x669e223fffff0fff 0xbb34f111fffff87f

def z435 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0xfe9e3e3ffc71ffff 0xfff4f1f1ffe38fff

def z436 : W := mkw 0x0236b2af2c510aac 0x4011b59579628855 0xe7fff3ff3c710fef 0xff3fff9ff9e3887f

def z437 : W := mkw 0x17203f709683fd41 0x80b901fb84b41fea 0xdf003ff8ff81fffe 0xfef801ffc7fc0fff

def z438 : W := mkw 0x48f0d4f321c6c788 0x224786a7990e363c 0xd9f1ffff23cecf97 0xfecf8ffff91e767c

def z439 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd8603c00c00ff01e 0x76c301e006007f80

def z440 : W := mkw 0x0016000d285002ac 0x4000b00069428015 0x609e203f007101ef 0x3304f101f803880f

def z441 : W := mkw 0x0000041000001040 0x8000002080000082 0x00002c1800013060 0x00000160c0000983

def z442 : W := mkw 0x402090e30082c780 0x220104871804163c 0xc06013e7004ecf97 0x5603009f3802767c

def z443 : W := mkw 0x802494be00000000 0x040124a5f0000000 0x0000003f00000000 0x00000001f8000000

def z444 : W := mkw 0x4236b2ef2cd3cfac 0x6211b59779669e7d 0xe69e33ff3c71cfef 0xbf34f19ff9e38e7f

def z445 : W := mkw 0x1dd9400021440008 0x00eeca00010a2000 0x3fffc00023ce0015 0xf9fffe00011e7000

def z446 : W := mkw 0x0020143000025140 0x800100a18000128a 0x00000038000001e0 0x00000001c000000f

def z447 : W := mkw 0x970d2b0c00000000 0x04b8695860000000 0x260e000000000000 0x0130700000000000

def z448 : W := mkw 0x48f0547161eed7d8 0xa24782a38b0f76be 0xd8e03c38e3ffffff 0x7ec701e1c71fffff

def z449 : W := mkw 0x3509400093040002 0x01a84a0004982000 0x0101c00003800000 0x00080e00001c0000

def z450 : W := mkw 0x4000c0c201848400 0x22000606100c2420 0x0101c1c003800000 0x00080e0e001c0000

def z451 : W := mkw 0x4230f2e325c7cf88 0x22118797192e3e7c 0xc771f3e73fcfcf9f 0xfe3b8f9f39fe7e7c

def z452 : W := mkw 0x1500000092000000 0x00a8000004900000 0x070000003f800000 0x8838000001fc0000

def z453 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0x1f002fc0ff813e08 0xa8f8017e07fc09f0

def z454 : W := mkw 0xdffdffff61eed7d8 0xa6ffeffffb0f76be 0xffffffffe3ffffff 0xffffffffff1fffff

def z455 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x269e203f1c7101e9 0x2134f101f8e3880f

def z456 : W := mkw 0x9fe9bfb200000000 0x04ff4dfd90000000 0x9f61ffc000000002 0xf4fb0ffe00000000

def z457 : W := mkw 0x150009409681ac01 0x00a8004a04b40d60 0xd9001dc0ff81fe1c 0x4ec800ee07fc0ff0

def z458 : W := mkw 0x08c0041000000000 0x0046002080000000 0x18802c1800000000 0x20c40160c0000000

def z459 : W := mkw 0x17002b4000808400 0x00b8015a00040420 0xdf003fc02380ce16 0xfef801fe011c0670

def z460 : W := mkw 0x08c0000040280010 0x0046000002014000 0x58e02038c07f01ff 0x72c70101c603f80f

def z461 : W := mkw 0x0000000000000000 0x0000000000000000 0x40000000c001f01c 0x0200000006000f80

def z462 : W := mkw 0xc224bfff0082c780 0x261125fff804163c 0xc0003fff0000cf82 0x060001fff800067c

def z463 : W := mkw 0x48f0d4f361eed7d8 0xa24786a79b0f76be 0xd971dfe7e3ceff97 0xdecb8eff3f1e77fc

def z464 : W := mkw 0x7ffff2efffffcfbe 0x63ffff977ffffe7d 0xfffff3ffffffcfff 0xffffff9ffffffe7f

def z465 : W := mkw 0x0200220004010800 0x0010011000200840 0x060020001c010008 0x2030010000e00800

def z466 : W := mkw 0x5736fbefbfd7efad 0x62b9b7df7dfebf7d 0xffffffffffffffff 0xffffffffffffffff

def z467 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0x40e00038c07ff1fd 0x02070001c603ff8f

def z468 : W := mkw 0x1dc9000000000000 0x00ee480000000000 0x3e8e000000000000 0x21f4700000000000

def z469 : W := mkw 0x1fdf220d2c510aac 0x40fef91069628855 0x7fffe23f3c710fef 0xfbffff11f9e3887f

def z470 : W := mkw 0x4236f2ef2dd7cfac 0x6211b797796ebe7d 0xe77fd3e73fcecf97 0xdf3bfe9f39fe767c

def z471 : W := mkw 0x00000000402a5150 0x800000000201528a 0x00000000c00ef010 0x0000000006007780

def z472 : W := mkw 0x150009409280a401 0x00a8004a04940520 0x9f001dc0ff80f01c 0xfcf800ee07fc0780

def z473 : W := mkw 0x3fdf620cfb7c001e 0x01fefb1067dbe000 0x3fffe23ffffe001f 0xf9ffff11fffff000

def z474 : W := mkw 0x3dc94000d32c0012 0x01ee4a0006996000 0x3fffc000c38e0011 0xf1fffe00061c7000

def z475 : W := mkw 0x5530d0e3b3c6c788 0x22a986871d9e363c 0xdf71d3e7ffcecf9f 0xfefb8e9f3ffe767c

def z476 : W := mkw 0x7ffbfbe3ffffef9f 0x23ffdfdf1fffff7c 0xffffffe7ffffff9f 0xffffffff3ffffffc

def z477 : W := mkw 0xbde9ddb2d32c0012 0x05ef4eed96996000 0x9961ddc0c38e0010 0x44cb0eee061c7000

def z478 : W := mkw 0x00120041bed1aead 0x400090020df68d75 0x40000000fff1fffc 0x0a00000007ff8fff

def z479 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x661e02273c400f87 0x9b30f01139e2007c

def z480 : W := mkw 0x4234f2ef21c6c788 0x2211a797790e363c 0xe7fff3ff23cecf97 0xff3fff9ff91e767c

def z481 : W := mkw 0x17162b0d2c510aac 0x40b8b15869628855 0xff9e3fff3c710fef 0xfffcf1fff9e3887f

def z482 : W := mkw 0x9de99db2402a5150 0x84ef4ced9201528a 0xd9e1fdf8c07ff1ff 0x76cf0fefc603ff8f

def z483 : W := mkw 0x753bd0e3bbd6c78e 0x23a9de871ddeb63c 0xe77fd3e73fcecf97 0xdf3bfe9f39fe767c

def z484 : W := mkw 0x0204220c00000000 0x0010211060000000 0x268e201800000000 0x21347100c0000000

def z485 : W := mkw 0x9ded94be00000000 0x04ef6ca5f0000000 0x3fffc03f00000001 0xf1fffe01f8000000

def z486 : W := mkw 0x021222012c510aac 0x4010911009628855 0x460022003c710fee 0xba30011001e3887f

def z487 : W := mkw 0x08c0041040281050 0x8046002082014082 0x18e02c18c07f307d 0x70c70160c603f983

def z488 : W := mkw 0x0ae4363c00000000 0x005721b1e0000000 0xbefe3e3f00000003 0xf5f7f1f1f8000000

def z489 : W := mkw 0x08e0143000000000 0x004700a180000000 0x00e0003800000001 0x00070001c0000000

def z490 : W := mkw 0x8ae4bfbe00000000 0x045725fdf0000000 0x98e03fff00000003 0x74c701fff8000000

def z491 : W := mkw 0x08e094b200000000 0x004704a590000000 0x99f1ffff00000003 0xf4cf8ffff8000000

def z492 : W := mkw 0x1dc9000092000000 0x00ee480004900000 0x3fffc000ff80001d 0xf9fffe0007fc0000

def z493 : W := mkw 0x17002b0000000000 0x00b8015800000000 0xdf003fc0c001f01e 0xf6f801fe06000f80

def z494 : W := mkw 0x0204220d04010aa0 0x4010211068200855 0x4600223f3c010fee 0xba300111f9e0087f

def z495 : W := mkw 0x001200002850000c 0x0000900001428000 0x000000003c70000c 0x0800000001e38000

def z496 : W := mkw 0x972dbfbe00000000 0x04b96dfdf0000000 0xa71fffff00000002 0x8538fffff8000000

def z497 : W := mkw 0x57106b41b7c7ef89 0x22b8835a0dbe3f7c 0xdf003fc0ffcfff9e 0xfef801fe07fe7ffc

def z498 : W := mkw 0x88e994b200000000 0x04474ca590000000 0x0061c00000000000 0x00030e0000000000

def z499 : W := mkw 0x28fb5430697e515e 0x8147daa1834bf28a 0xf8fffc38c07ff1ff 0x77c7ffe1c603ff8f

def z500 : W := mkw 0x0206220d0c110aa4 0x4010311068608855 0x668e223f1c310fea 0x23347111f8e1887f

def z501 : W := mkw 0x0216220c2c51082c 0x4010b11061628841 0x269e20183c71006d 0xb934f100c1e38803

def z502 : W := mkw 0x1fe03f30402a5150 0x80ff01f98201528a 0xdfe03ff8c07ff1ff 0xf6ff01ffc603ff8f

def z503 : W := mkw 0x0200220004010800 0x0010011000200840 0xde003e00fc01fe1e 0xfef001f007e00ff0

def z504 : W := mkw 0x9fedbffe0481ac01 0x04ff6dfff0240d60 0xffffffff0001fe03 0xf7fffffff8000ff0

def z505 : W := mkw 0x20124000697c001e 0x01009200034be000 0x00000000007e0000 0x000000000003f000

def z506 : W := mkw 0x3fdf220dfe790abe 0x41fef9106ff3c855 0x7e9e223ffc710fef 0xbbf4f111ffe3887f

def z507 : W := mkw 0x3dcb0000da380016 0x01ee580006d1c000 0x3f8e0000ffb0001c 0xf9fc700007fd8000

def z508 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0x98e03c38c00ef013 0x74c701e1c6007780

def z509 : W := mkw 0x9fedbfbe40281050 0x84ff6dfdf2014082 0xbfffffffc031306b 0xf5fffffffe018983

def z510 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x269e223f3c000e03 0xb934f111f9e00070

def z511 : W := mkw 0x3dc94940d3aca413 0x01ee4a4a069d6520 0x9961ddc0c38ef010 0x44cb0eee061c7780

def z512 : W := mkw 0x08e0143000000000 0x004700a180000000 0x98601c0000000000 0x44c300e000000000

def z513 : W := mkw 0x1500090000000000 0x00a8004800000000 0x99001dc000000000 0x44c800ee00000000

def z514 : W := mkw 0x1fc02b40d6a9ac11 0x00fe015a06b54d60 0xdfe03fc0fffffe1f 0xfeff01fe07fffff0

def z515 : W := mkw 0x8204ab8e00000000 0x0410255c70000000 0x000003c700000000 0x0000001e38000000

def z516 : W := mkw 0x8aedbfbe00000000 0x04576dfdf0000000 0xa0ffffff00000003 0x0507fffff8000000

def z517 : W := mkw 0x5720bbe39683ef81 0x22b905df1cb41f7c 0xdf003fe7ff81ff9e 0xfef801ff3ffc0ffc

def z518 : W := mkw 0xbfcf2f1cda380016 0x05fe7978e6d1c000 0x3e8e2c18dc300008 0x21f47160c6e18000

def z519 : W := mkw 0x17002b0004010800 0x00b8015800200840 0xdf003fc03c010e0e 0xfef801fe01e00870

def z520 : W := mkw 0x02002b400481ac01 0x0010015a00240d60 0xd8003fc0c001fe1e 0x76c001fe06000ff0

def z521 : W := mkw 0x0000000000000000 0x0000000000000000 0x008000000070000d 0x3004000000038000

def z522 : W := mkw 0x0000000000000000 0x0000000000000000 0x40002038000101e2 0x02000101c000080f

def z523 : W := mkw 0x17062b0c9e112825 0x40b8315864f08941 0x3e8e2c18dc313068 0x21f47160c6e18983

def z524 : W := mkw 0x28db4000697c001e 0x0146da00034be000 0x26ffc0003c7e000d 0xb937fe0001e3f000

def z525 : W := mkw 0x1fcd220c00000000 0x00fe691060000000 0x3fffe23f00000003 0xf1ffff11f8000000

def z526 : W := mkw 0x17002b0096012801 0x00b8015804b00940 0x060000001c000000 0x0030000000e00000

def z527 : W := mkw 0x88ed94be00000000 0x04476ca5f0000000 0xb8fffc3f00000003 0x75c7ffe1f8000000

def z528 : W := mkw 0x4010404161eed7d8 0xa20082020b0f76be 0x40000000e3fffffc 0x0a000000071fffff

def z529 : W := mkw 0x3dcb0000da380016 0x01ee580006d1c000 0x3eee0000dc7e001d 0x71f7700006e3f000

def z530 : W := mkw 0x4030d0a321464388 0x22018685190a321c 0x8171d3e7004e0183 0xd40b8e9f3802700c

def z531 : W := mkw 0x371b6b40bfd5ac0f 0x01b8db5a05fead60 0xff1fffc0ff81fe1e 0xfff8fffe07fc0ff0

def z532 : W := mkw 0x351b4000fb7c001e 0x01a8da0007dbe000 0x271fc000fffe001c 0x8938fe0007fff000

def z533 : W := mkw 0x17042b0c00000000 0x00b8215860000000 0xbf9e3fff00000003 0xf5fcf1fff8000000

def z534 : W := mkw 0x00120001285002ac 0x4000900009428015 0x00000000007001e0 0x000000000003800f

def z535 : W := mkw 0xbfedffbed32c0012 0x05ff6ffdf6996000 0xbfffffffc38e0013 0xf5fffffffe1c7000

def z536 : W := mkw 0x08f05430616e5158 0x804782a1830b728a 0xd9f1fc38e3fff1ff 0xfecf8fe1c71fff8f

def z537 : W := mkw 0xc8fdd4bf21464388 0x2647eea5f90a321c 0x20ffc03f004e0181 0x0107fe01f802700c

def z538 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0x9f003dc0df81f018 0x64f801ee06fc0f80

def z539 : W := mkw 0x0200220004010800 0x0010011000200840 0x468022383c710fef 0xba340111c1e3887f

def z540 : W := mkw 0x001200012c510aac 0x4000900009628855 0x669e00003c710fed 0xbb34f00001e3887f

def z541 : W := mkw 0x0016000d285002ac 0x4000b00069428015 0x269e003f3c7001ed 0xb934f001f9e3800f

def z542 : W := mkw 0xdfedbfff0082c780 0x26ff6dfff804163c 0xffffffff0000cf83 0xf7fffffff800067c

def z543 : W := mkw 0x17162b4dbed1aead 0x40b8b15a6df68d75 0xff1e3fc7ff81fe1e 0xfff8f1fe3ffc0ff0

def z544 : W := mkw 0x9dc90d1000000000 0x04ee486880000000 0x18000c0000000000 0x00c0006000000000

def z545 : W := mkw 0x3ddb0000fa78001e 0x01eed80007d3c000 0x3e9e0000fc70000d 0xb9f4f00007e38000

def z546 : W := mkw 0x28c94000412c0012 0x01464a0002096000 0x0061c000000e0000 0x00030e0000007000

def z547 : W := mkw 0x9fffbfbf285002ac 0x44fffdfdf9428015 0xbfffffff007001e3 0xf5fffffff803800f

def z548 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0x18e00038c07e01fd 0x70c70001c603f00f

def z549 : W := mkw 0x0010004120c08688 0x0000800209060434 0xc11013e723c0cf97 0xde08809f391e067c

def z550 : W := mkw 0x800d808e00000000 0x04006c0470000000 0x201fc00700000000 0x0100fe0038000000

def z551 : W := mkw 0x28db4000fb7c001e 0x0146da0007dbe000 0x20ffc000fffe001d 0x0907fe0007fff000

def z552 : W := mkw 0x20020000da380016 0x0100100006d1c000 0x00000000dc300008 0x0000000006e18000

def z553 : W := mkw 0x17042b4d9681aea1 0x40b8215a6cb40d75 0xdf003fffff81fffe 0xfef801fffffc0fff

def z554 : W := mkw 0x150000409681ac01 0x00a8000204b40d60 0x5f000000ff81fe1c 0xfaf8000007fc0ff0

def z555 : W := mkw 0x1de01d70d2aaf551 0x80ef00eb869557aa 0x99601dc0c38ef010 0x44cb00ee061c7780

def z556 : W := mkw 0x0020143000025140 0x800100a18000128a 0xd8003c38c001f1fe 0x76c001e1c6000f8f

def z557 : W := mkw 0x0000000000000000 0x0000000000000000 0x060000003c00000c 0xb830000001e00000

def z558 : W := mkw 0x15120000ba50000c 0x00a8900005d28000 0x3f9e0000fff0001d 0xf9fcf00007ff8000

def z559 : W := mkw 0x403090e320c2c788 0x220184871906163c 0xc01013e72040cf87 0x9e00809f3902067c

def z560 : W := mkw 0x4020d0e20186c500 0x22010687100c3628 0x8171d3e7038ec013 0xd40b8e9f381c7600

def z561 : W := mkw 0x0206220c0c110824 0x4010311060608841 0x668e22183c310e6e 0xbb347110c1e18873

def z562 : W := mkw 0x08c0000040280010 0x0046000002014000 0xd8e03c00c07ff01f 0x76c701e00603ff80

def z563 : W := mkw 0x0020143000025140 0x800100a18000128a 0x80001c000000f000 0x040000e000000780

def z564 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0x98e01c38c07ef1f1 0x44c700e1c603f78f

def z565 : W := mkw 0x3de95430d32e5152 0x81ef4aa18699728a 0xd9e1fc38c3fff1ff 0x76cf0fe1c61fff8f

def z566 : W := mkw 0x4216e2cf2dd58eac 0x6210b716796eac75 0x679fe3ff3ff10fef 0xbb3cff1ff9ff887f

def z567 : W := mkw 0xc8fdd4ff21c6c788 0x2647eea7f90e363c 0xe1ffd3ff23cecf97 0xdf0ffe9ff91e767c

def z568 : W := mkw 0x3dc94000d32c0012 0x01ee4a0006996000 0x19e1c000c3fe001d 0x70cf0e00061ff000

def z569 : W := mkw 0x20124000fb7e515e 0x8100920007dbf28a 0x40000000fffff1fc 0x0a00000007ffff8f

def z570 : W := mkw 0x08c0041040281050 0x8046002082014082 0xd8803c18c031f07e 0x76c401e0c6018f83

def z571 : W := mkw 0x0ae4363d442b5bf0 0xc05721b1ea215adf 0xd8e03e3fc07fffff 0x76c701f1fe03ffff

def z572 : W := mkw 0x3dfb5020fb7e411e 0x01efda8107dbf208 0xffffd020fffec19f 0xfffffe8107fff60c

def z573 : W := mkw 0x3dfb5430fb7c001e 0x01efdaa187dbe000 0xbffffc38fffe001f 0xfdffffe1c7fff000

def z574 : W := mkw 0x1de91430402a5150 0x80ef48a18201528a 0xfffffc38c07ff1ff 0xf7ffffe1c603ff8f

def z575 : W := mkw 0x0002000008100004 0x0000100000408000 0x268e00001c300008 0x2134700000e18000

def z576 : W := mkw 0xbdfbddb2fb7c001e 0x05efdeed97dbe000 0xbfffddc0fffe001d 0xfdfffeee07fff000

def z577 : W := mkw 0x9fedbffe9681ac01 0x04ff6dfff4b40d60 0xbfffffff3f800e03 0xfdfffffff9fc0070

def z578 : W := mkw 0x48f0d4b3616e53d8 0xa24786a59b0b729e 0x00f1c03f007e01e1 0x00078e01f803f00f

def z579 : W := mkw 0x08d04000616c0018 0x00468200030b6000 0x19f1c000e3fe001d 0xf8cf8e00071ff000

def z580 : W := mkw 0x3ddf400dfb7c02be 0x41eefa006fdbe015 0x3fffc03ffffe01fd 0xf9fffe01fffff00f

def z581 : W := mkw 0x17122b40bed1ac0d 0x00b8915a05f68d60 0xff9e3fc0fff1fe1f 0xfffcf1fe07ff8ff0

def z582 : W := mkw 0x4030d4f321c6d7c8 0xa20186a7990e36be 0xc171ffff23cffff7 0xde0b8ffff91e7fff

def z583 : W := mkw 0x9fedbffe00808400 0x04ff6dfff0040420 0xffffffff2380ce17 0xfffffffff91c0670

def z584 : W := mkw 0x1500090092002001 0x00a8004804900100 0x18000c00c0003000 0x00c0006006000180

def z585 : W := mkw 0x0216220d6c7b5bfc 0xc010b1106b63dadf 0x669e223ffc7fffff 0xbb34f111ffe3ffff

def z586 : W := mkw 0x7de9d0e2d3aec512 0x23ef4e87169d7628 0x9961d1c0c38ec010 0x44cb0e8e061c7600

def z587 : W := mkw 0x1fe03f709681ac01 0x00ff01fb84b40d60 0xdfe03ff8ff81fe1f 0xfeff01ffc7fc0ff0

def z588 : W := mkw 0x5520d9e29386e501 0x22a906cf149c3728 0x9961ddc0c38ef010 0x44cb0eee061c7780

def z589 : W := mkw 0x0000000000000000 0x0000000000000000 0x00800038007001e1 0x00040001c003800f

def z590 : W := mkw 0x17002b0096012801 0x00b8015804b00940 0x5e002e00fc013e0e 0xbaf0017007e009f0

def z591 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0x3effec3f00000001 0x21f7ff61f8000000

def z592 : W := mkw 0x15104000b3440008 0x00a88200059a2000 0x1f71c000ffce001d 0xf8fb8e0007fe7000

def z593 : W := mkw 0x000200000c110824 0x4000100000608841 0x000000001c310068 0x0000000000e18803

def z594 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xc7003fc03f81fe02 0x8e3801fe01fc0ff0

def z595 : W := mkw 0x9fffbfffbed1aead 0x44fffdfffdf68d75 0xfffffffffff1ffff 0xffffffffffff8fff

def z596 : W := mkw 0x3ddb4940fbfca41f 0x01eeda4a07dfe520 0xbfffddc0fffef01d 0xfdfffeee07fff780

def z597 : W := mkw 0xdfffffff2dd7cfac 0x66fffffff96ebe7d 0xffffffff3fffcfff 0xfffffffff9fffe7f

def z598 : W := mkw 0x9fedbffe9280a401 0x04ff6dfff4940520 0xbfffffffc380f013 0xf5fffffffe1c0780

def z599 : W := mkw 0x4036d0af295643ac 0x6201b685794ab21d 0x20ffc03f007e01e1 0x0107fe01f803f00f

def z600 : W := mkw 0x08e0143040280010 0x004700a182014000 0x98e03c38c07e001f 0x74c701e1c603f000

def z601 : W := mkw 0x5710ebc3b7c5ae89 0x22b8875e1dbe2d74 0xdf11ffc7ff81fe1e 0xfef88ffe3ffc0ff0

def z602 : W := mkw 0x000000409681ac01 0x0000000204b40d60 0xc10013c0ff81fe1e 0xde08009e07fc0ff0

def z603 : W := mkw 0x001200016c7b5bfc 0xc00090000b63dadf 0x40000000fc7ffffc 0x0a00000007e3ffff

def z604 : W := mkw 0x1500000092000000 0x00a8000004900000 0xdf003c00ff81f01e 0xfef801e007fc0f80

def z605 : W := mkw 0x0020102000000000 0x0001008100000000 0x8060102000000003 0x5403008100000000

def z606 : W := mkw 0x17002b400481ac01 0x00b8015a00240d60 0xdf003fc00001fe02 0xf6f801fe00000ff0

def z607 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc00013e723cecf96 0x0e00009f391e767c

def z608 : W := mkw 0x0006000c08100024 0x4000300060408001 0x208e001800300060 0x01047000c0018003

def z609 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3f9fc000ffb00008 0xa9fcfe0007fd8000

def z610 : W := mkw 0x3ddb4000bb54000e 0x01eeda0005daa000 0x3fffc0003f800001 0xf9fffe0001fc0000

def z611 : W := mkw 0x402090a300024380 0x220104851800121c 0x0000002700000180 0x000000013800000c

def z612 : W := mkw 0x4010404121c6c788 0x22008202090e363c 0xc10013c023cecf96 0xde08009e011e767c

def z613 : W := mkw 0x5df9d0e321c6c788 0x22efce87190e363c 0xffffd3e723cecf97 0xfffffe9f391e767c

def z614 : W := mkw 0x1500000000000000 0x00a8000000000000 0x1f00000000000000 0xf0f8000000000000

def z615 : W := mkw 0x3ddb4040fbfc841e 0x01eeda0207dfe420 0xffffd3c0fffece1f 0xfffffe9e07fff670

def z616 : W := mkw 0x201b40002954000e 0x0100da00014aa000 0x201fc00000000000 0x0100fe0000000000

def z617 : W := mkw 0x0000004000808400 0x0000000200040420 0x010003c023800e00 0x8808001e011c0070

def z618 : W := mkw 0x0000000000024100 0x0000000000001208 0x40000000004ec194 0x020000000002760c

def z619 : W := mkw 0x08e0147040aad550 0x804700a3820556aa 0xd9e03ff8e3ffffff 0xfecf01ffc71fffff

def z620 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x668e20183c710fec 0x2b347100c1e3887f

def z621 : W := mkw 0x5730fbe3b7c7ef89 0x22b987df1dbe3f7c 0xc771d3e73fcecf97 0xde3b8e9f39fe767c

def z622 : W := mkw 0x1fc02f50d6a9bc51 0x80fe017a86b54de2 0xdf803fd8ffb1fe7e 0xfefc01fec7fd8ff3

def z623 : W := mkw 0x002090a200000000 0x0001048510000000 0x0071c02700000001 0x00038e0138000000

def z624 : W := mkw 0x3fdb6b00ff7d281f 0x01fedb5807fbe940 0x3fffec00ffff301d 0xf9ffff6007fff980

def z625 : W := mkw 0x970dabce9681ac01 0x04b86d5e74b40d60 0x271fc3c73f800e00 0x8938fe1e39fc0070

def z626 : W := mkw 0x02002b400481ac01 0x0010015a00240d60 0xc1003fc02381fe16 0xde0801fe011c0ff0

def z627 : W := mkw 0x1fc92b409681ac01 0x00fe495a04b40d60 0xffffffc0ff81fe1f 0xfffffffe07fc0ff0

def z628 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0x18e02c38c07f31e9 0x20c70161c603f98f

def z629 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3effc000dc7e0009 0x21f7fe0006e3f000

def z630 : W := mkw 0x7df9d0e3f3eec79a 0x23efce871f9f763c 0xd971d3e7e3cecf97 0xdecb8e9f3f1e767c

def z631 : W := mkw 0x02203f700483fd41 0x801101fb80241fea 0xc0003ff80001ffe2 0x060001ffc0000fff

def z632 : W := mkw 0x5530d9e3b3c6e789 0x22a986cf1d9e373c 0xd971dfe7e3ceff97 0xdecb8eff3f1e77fc

def z633 : W := mkw 0x4020d0a201064100 0x2201068510083208 0x0061c000000e0000 0x00030e0000007000

def z634 : W := mkw 0x0030502021464108 0x00018281010a3208 0xc171d02023cec197 0xde0b8e81011e760c

def z635 : W := mkw 0x0ad6261d6c791afc 0xc056b130eb63c8d7 0x7e9e2e3ffc713fef 0xbbf4f171ffe389ff

def z636 : W := mkw 0x9de99df29280a401 0x04ef4cef94940520 0x9961ddc0c380f010 0x44cb0eee061c0780

def z637 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xde003fc0dc01fe0a 0x26f001fe06e00ff0

def z638 : W := mkw 0x3fcb2b40deb9ac17 0x01fe595a06f5cd60 0xff8e3fc0ffb1fe1e 0xfffc71fe07fd8ff0

def z639 : W := mkw 0x8236bfbf2c510aac 0x4411b5fdf9628855 0xe69e3fff3c710fef 0xbf34f1fff9e3887f

def z640 : W := mkw 0x7dfbd0e2fbfec51e 0x23efde8717dff628 0xbfffd1c0fffec01d 0xfdfffe8e07fff600

def z641 : W := mkw 0x002090a200000000 0x0001048510000000 0x8161d1c000000000 0x440b0e8e00000000

def z642 : W := mkw 0x3fdb6200ff7d081e 0x01fedb1007fbe840 0x7fffe200ffff0e1f 0xfbffff1007fff870

def z643 : W := mkw 0x0000000000000000 0x0000000000000000 0x0010022700000003 0x9000801138000000

def z644 : W := mkw 0x0000000000000000 0x0000000000000000 0x18000000c000001c 0x70c0000006000000

def z645 : W := mkw 0x0000000000000000 0x0000000000000000 0xc0003c000001f002 0x060001e000000f80

def z646 : W := mkw 0xb71feb8ebb54000e 0x05b8ff5c75daa000 0x271fc3c73f800000 0x8938fe1e39fc0000

def z647 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0x00600000000e0000 0x0003000000007000

def z648 : W := mkw 0x88ff94bf285002ac 0x4447fca5f9428015 0x20ffc03f007001e1 0x0107fe01f803800f

def z649 : W := mkw 0x1500000092000000 0x00a8000004900000 0x1e000000dc000008 0x20f0000006e00000

def z650 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0x98e01c00c07ef01d 0x74c700e00603f780

def z651 : W := mkw 0x0020102000024100 0x0001008100001208 0xc00010200000c182 0x060000810000060c

def z652 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd8601c20c04ef197 0x56c300e10602778c

def z653 : W := mkw 0xbffffffefffdac1f 0x05fffffff7ffed60 0xfffffffffffffe1f 0xfffffffffffffff0

def z654 : W := mkw 0x00201020402a5150 0x800100810201528a 0xc0601020c07ff1ff 0x560300810603ff8f

def z655 : W := mkw 0x9fed3f3c402a5150 0x84ff69f9e201528a 0xfeee3c38c07ff1ff 0x77f771e1c603ff8f

def z656 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x1961c000fffe001c 0x48cb0e0007fff000

def z657 : W := mkw 0x0000000000000000 0x0000000000000000 0x810013c000000002 0xd408009e00000000

def z658 : W := mkw 0x4216e2cf2dd58eac 0x6210b716796eac75 0x271fc3c73f800e00 0x8938fe1e39fc0070

def z659 : W := mkw 0x0020102000024100 0x0001008100001208 0x00600020004e0181 0x000300010002700c

def z660 : W := mkw 0x9fcd2f1c00000000 0x04fe6978e0000000 0xbf8e3fd800000002 0xf5fc71fec0000000

def z661 : W := mkw 0x08c00000402a5150 0x804600000201528a 0x58e00000c07ff1fd 0x72c700000603ff8f

def z662 : W := mkw 0x08e0143000000000 0x004700a180000000 0xd8e03c38007101ef 0x76c701e1c003880f

def z663 : W := mkw 0x4020d0e20186c500 0x22010687100c3628 0xc161d1e003cec197 0x560b0e8f001e760c

def z664 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0x5e002c00ff81fe1c 0x2af0016007fc0ff0

def z665 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc161d1c023cecf94 0x4e0b0e8e011e767c

def z666 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x661e22073c010e0e 0xbb30f11039e00870

def z667 : W := mkw 0x1fe03f30d62b7951 0x80ff01f986b15bca 0xdee03c38dc7ff1ff 0x76f701e1c6e3ff8f

def z668 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc111d3e72380cf82 0x8e088e9f391c067c

def z669 : W := mkw 0x001200002850000c 0x0000900001428000 0x669e20383c7101ef 0xbb34f101c1e3880f

def z670 : W := mkw 0x20124000fb7c001e 0x0100920007dbe000 0x0171c000fffe001d 0xd80b8e0007fff000

def z671 : W := mkw 0x0020102000024100 0x0001008100001208 0xc0e03038007fc1ff 0x76070181c003fe0f

def z672 : W := mkw 0x17002b0096012801 0x00b8015804b00940 0xde003c00dc01f01e 0x76f001e006e00f80

def z673 : W := mkw 0x0214220d24410aa8 0x4010a11069220855 0x4010223f20410fe7 0x9a008111f902087f

def z674 : W := mkw 0x08c0000000000000 0x0046000000000000 0x18e0000000000001 0x70c7000000000000

def z675 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x661e02073c710fec 0x8b30f01039e3887f

def z676 : W := mkw 0x02002b409681ac01 0x0010015a04b40d60 0xc0003fc0ff81fe1e 0x0e0001fe07fc0ff0

def z677 : W := mkw 0x0000000000000000 0x0000000000000000 0x4000002000400187 0x120000010002000c

def z678 : W := mkw 0x3ddb4000fb7e515e 0x81eeda0007dbf28a 0x7fffc000fffff1fd 0xfbfffe0007ffff8f

def z679 : W := mkw 0xfffffffffbfec79e 0x27ffffffffdff63c 0xfffffffffffecf9f 0xfffffffffffff67c

def z680 : W := mkw 0x08c0041040281050 0x8046002082014082 0x18000c00c0003000 0x00c0006006000180

def z681 : W := mkw 0x0010000120400288 0x0000800009020014 0x4090223f20710fef 0xba048111f903887f

def z682 : W := mkw 0xdde9ddf20186c500 0x26ef4eef900c3628 0x9961ddc0038ec010 0x44cb0eee001c7600

def z683 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0x1f0003c0ff800e1c 0xf8f8001e07fc0070

def z684 : W := mkw 0x0ae03f7044abfd51 0x805701fb82255fea 0xd8e03ff8c07fffff 0x76c701ffc603ffff

def z685 : W := mkw 0x9ffdbfbf20400288 0x04ffedfdf9020014 0xffffffff20400f87 0xfffffffff902007c

def z686 : W := mkw 0x1716220dbe510aac 0x40b8b1106df28855 0x7f9e223ffff10fff 0xfbfcf111ffff887f

def z687 : W := mkw 0x08f6143d687a53fc 0xc047b0a1eb43d29f 0x20fe003f007e01e1 0x0107f001f803f00f

def z688 : W := mkw 0x0010000120400288 0x0000800009020014 0x0010002700400181 0x000080013802000c

def z689 : W := mkw 0x1fe03f3000000000 0x00ff01f980000000 0x9fe03ff800000003 0xf4ff01ffc0000000

def z690 : W := mkw 0x17162b4dbed1aead 0x40b8b15a6df68d75 0x679e23ff3ff10fef 0xbb3cf11ff9ff887f

def z691 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x609e223f00710fe3 0x0304f111f803887f

def z692 : W := mkw 0x0000000000000000 0x0000000000000000 0xd8803c38c071f1ff 0x76c401e1c6038f8f

def z693 : W := mkw 0x28db4000697c001e 0x0146da00034be000 0x21ffc00023fe0015 0xd90ffe00011ff000

def z694 : W := mkw 0x3deb1430da3a5156 0x81ef58a186d1d28a 0xfeee3c38dc7ff1ff 0x77f771e1c6e3ff8f

def z695 : W := mkw 0x6032d0e3fbfec79e 0x230196871fdff63c 0xc171d3e7fffecf9f 0xde0b8e9f3ffff67c

def z696 : W := mkw 0x0af6363d6c7b5bfc 0xc057b1b1eb63dadf 0x66fe223f3c7f0fef 0xbb37f111f9e3f87f

def z697 : W := mkw 0x0224363d04035be0 0xc01121b1e8201adf 0xc0003e3f0001ffe2 0x060001f1f8000fff

def z698 : W := mkw 0x8224bfbe00000000 0x041125fdf0000000 0xa69e3fff00000003 0xb534f1fff8000000

def z699 : W := mkw 0xc234ffff21c6c788 0x2611a7fff90e363c 0xc171ffff23cecf97 0xde0b8ffff91e767c

def z700 : W := mkw 0x88cd041c00000000 0x04466820e0000000 0x208e001800000000 0x01047000c0000000

def z701 : W := mkw 0x3fdf6b4dfffdaebf 0x41fefb5a6fffed75 0xffffffffffffffff 0xffffffffffffffff

def z702 : W := mkw 0x0030102120424388 0x000180810902121c 0xc0701227204ecf97 0xde0380913902767c

def z703 : W := mkw 0x0200220004010800 0x0010011000200840 0x4000220000010e02 0x0200011000000870

def z704 : W := mkw 0x3fcf220cde390836 0x41fe791066f1c841 0x3e8e2018dc310068 0x21f47100c6e18803

def z705 : W := mkw 0x17122b41bed1aead 0x40b8915a0df68d75 0xdf003fc0fff1fffe 0xfef801fe07ff8fff

def z706 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc071d3e7004ecf83 0x06038e9f3802767c

def z707 : W := mkw 0x4030d4f321c6d7c8 0xa20186a7990e36be 0xc1f1ffff23ffffff 0xfe0f8ffff91fffff

def z708 : W := mkw 0x8aedbfbe00000000 0x04576dfdf0000000 0xb8ffffff00000003 0x75c7fffff8000000

def z709 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0x8171d3c723cece15 0xdc0b8e9e391e7670

def z710 : W := mkw 0x401240412dd7cfac 0x62009202096ebe7d 0x400000003fcecf94 0x0a00000001fe767c

def z711 : W := mkw 0x9fedbfbe92002001 0x04ff6dfdf4900100 0xbfffffffc0003003 0xf5fffffffe000180

def z712 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0xa71fffc700000002 0x8538fffe38000000

def z713 : W := mkw 0x6012404169fec79e 0x230092020b4ff63c 0x4000000023fecf94 0x0a000000011ff67c

def z714 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0x4171c3e723ce0f87 0x9a0b8e1f391e707c

def z715 : W := mkw 0x9fedbfbe04010800 0x04ff6dfdf0200840 0xffffffff00010e03 0xf7fffffff8000870

def z716 : W := mkw 0x28db4000697c001e 0x0146da00034be000 0x27ffc0003ffe001d 0xf93ffe0001fff000

def z717 : W := mkw 0x9fedbfbe00001040 0x84ff6dfdf0000082 0xbfffffff00013063 0xf5fffffff8000983

def z718 : W := mkw 0x0204220c04010800 0x0010211060200840 0x669e223f3c710fef 0xbb34f111f9e3887f

def z719 : W := mkw 0x820dab8e00000000 0x04106d5c70000000 0x201fc3c700000000 0x0100fe1e38000000

def z720 : W := mkw 0x2adb6b406dfdac1f 0x0156db5a036fed60 0xe0ffffc0007ffe03 0x0707fffe0003fff0

def z721 : W := mkw 0xdfdd6f5d21c6c788 0x26feeb7ae90e363c 0x7e8e2c1823cecf94 0x2bf47160c11e767c

def z722 : W := mkw 0x0200224004818c00 0x0010011200240c60 0xdf003fc0ff81fe1e 0xfef801fe07fc0ff0

def z723 : W := mkw 0x4226f2ee0d97cd24 0x62113797706cbe69 0xa7eff1d81fbfc078 0x653f7f8ec0fdfe03

def z724 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x7e9e223ffc710fff 0xfbf4f111ffe3887f

def z725 : W := mkw 0x1fe03f70d6abfd51 0x80ff01fb86b55fea 0x07e003f83ffe0fe1 0x883f001fc1fff07f

def z726 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x67ffe23f3c710fef 0xfb3fff11f9e3887f

def z727 : W := mkw 0x802d90ae00000000 0x04016c8570000000 0xa17fd3e700000003 0xd50bfe9f38000000

def z728 : W := mkw 0x001200012850028c 0x0000900009428014 0x669e223f3c710fef 0xbb34f111f9e3887f

def z729 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x3f1fefc700000000 0xa1f8ff7e38000000

def z730 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x269e223f3c700fe3 0xb934f111f9e3807f

def z731 : W := mkw 0x00000000402a5150 0x800000000201528a 0xd8803c38c07ff1ff 0x76c401e1c603ff8f

def z732 : W := mkw 0xc224bfff0483cfa0 0x661125fff8241e7d 0xc0003fff0001cfe2 0x060001fff8000e7f

def z733 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x7fffc000ffff01fd 0xfbfffe0007fff80f

def z734 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x66fe223f3c7f0fff 0xfb37f111f9e3f87f

def z735 : W := mkw 0xc224bfff0483ef81 0x261125fff8241f7c 0xc0003fff0001ff82 0x060001fff8000ffc

def z736 : W := mkw 0x88ed94fe9681ac01 0x04476ca7f4b40d60 0x60ffc03fff81fe1d 0x0b07fe01fffc0ff0

def z737 : W := mkw 0x972dbfbe00000000 0x04b96dfdf0000000 0x271fc3ff00000000 0x8138fe1ff8000000

def z738 : W := mkw 0x68f25471fbfed7de 0xa34792a38fdff6be 0xd8e03c38ffffffff 0x7ec701e1c7ffffff

def z739 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd8f03e3fc07ff1ff 0xf6c781f1fe03ff8f

def z740 : W := mkw 0x60124041fbfed7de 0xa30092020fdff6be 0x40000000fffffffc 0x0a00000007ffffff

def z741 : W := mkw 0x7deb90e3dabac796 0x23ef5c871ed5d63c 0xfe8e13e7dc30cf8a 0x27f4709f3ee1867c

def z742 : W := mkw 0x48f254716dffdffc 0xe24792a38b6ffeff 0xd8e03c38ffffffff 0x7ec701e1c7ffffff

def z743 : W := mkw 0x88ed94be402a5150 0x84476ca5f201528a 0xf9ffffffc07ff1ff 0xf7cffffffe03ff8f

def z744 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3f7fc000ffce0015 0xd9fbfe0007fe7000

def z745 : W := mkw 0x4030d0e321c6d7c8 0xa2018687190e36be 0xc171d3e723cffff7 0xde0b8e9f391e7fff

def z746 : W := mkw 0x9fedbfbe04012801 0x04ff6dfdf0200940 0xbfffffff00013003 0xf5fffffff8000980

def z747 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xbfffffffc07ef01f 0xf5fffffffe03f780

def z748 : W := mkw 0x48d0c4d361ec96d8 0xa24686269b0f64b6 0x1991efdfe3b13e68 0xa8cc8f7eff1d89f3

def z749 : W := mkw 0x9ded9dbe00000000 0x04ef6cedf0000000 0x21ffc1ff00000001 0x010ffe0ff8000000

def z750 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd8603c38c07ff1fe 0x46c301e1c603ff8f

def z751 : W := mkw 0x9fedbfbe96012801 0x04ff6dfdf4b00940 0xffffffffdc01f01f 0xf7fffffffee00f80

def z752 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x7fffc200fffe0e1f 0xfbfffe1007fff070

def z753 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0xfffffc38fffff1ff 0xffffffe1c7ffff8f

def z754 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3fffc227fffe001f 0xf9fffe113ffff000

def z755 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x669e203f3c710fed 0x2b34f101f9e3887f

def z756 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x279fc3c700000001 0xb13cfe1e38000000

def z757 : W := mkw 0x9fedbfbe96012801 0x04ff6dfdf4b00940 0xfffffffffc013e0f 0xffffffffffe009f0

def z758 : W := mkw 0x17092b409681ac01 0x00b8495a04b40d60 0xff1fffc0ff81fe1e 0xfff8fffe07fc0ff0

def z759 : W := mkw 0x1dc90000d2280010 0x00ee480006914000 0x3fffc000fffe001d 0xf9fffe0007fff000

def z760 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc171d3e723ffcfff 0xde0b8e9f391ffe7f

def z761 : W := mkw 0x0af6363d6c7b5bfc 0xc057b1b1eb63dadf 0xbe7e1e07fc0efe10 0xcdf3f0f03fe077f0

def z762 : W := mkw 0x8aedb6be00000000 0x04576db5f0000000 0xa7fff3ff00000003 0xf53fff9ff8000000

def z763 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xe7ffd3e723cecf97 0xff3ffe9f391e767c

def z764 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xbf7fdfc7c00ef010 0xc5fbfefe3e007780

def z765 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xfefe3c38c07ff1ff 0xf7f7f1e1c603ff8f

def z766 : W := mkw 0x972dbfbe00000000 0x04b96dfdf0000000 0xbf1fffff00000002 0xf5f8fffff8000000

def z767 : W := mkw 0x88ed94be00000000 0x04476ca5f0000000 0xa1ffd1ff00000001 0x450ffe8ff8000000

def z768 : W := mkw 0x9fedbfbed2280010 0x04ff6dfdf6914000 0xbffffffffffe001f 0xfdfffffffffff000

def z769 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd9e03c38e3fff1ff 0xfecf01e1c71fff8f

def z770 : W := mkw 0x60124041ffffcfbe 0x630092020ffffe7d 0x40000000ffffcffc 0x0a00000007fffe7f

def z771 : W := mkw 0x60124041ffffef9f 0x230092020fffff7c 0x40000000ffffff9c 0x0a00000007fffffc

def z772 : W := mkw 0x972dbfbe00025140 0x84b96dfdf000128a 0xe71fffff0001f1e2 0x8738fffff8000f8f

def z773 : W := mkw 0x351b4000fb7c001e 0x01a8da0007dbe000 0x277fc000fffe001d 0xd93bfe0007fff000

def z774 : W := mkw 0x9fedbfbe40280010 0x04ff6dfdf2014000 0xbfffffff007e0003 0xf5fffffff803f000

def z775 : W := mkw 0x4030d4f321c6c788 0x220186a7990e363c 0xc171ffff23cecf97 0xde0b8ffff91e767c

def z776 : W := mkw 0x1dd94000b3440008 0x00eeca00059a2000 0x3fffc000ffce001d 0xf9fffe0007fe7000

def z777 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3fffe038fffe001f 0xf9ffff01c7fff000

def z778 : W := mkw 0x9ded9dbe00000000 0x04ef6cedf0000000 0xb9fffdff00000003 0x75cfffeff8000000

def z779 : W := mkw 0x970dab8e96012801 0x04b86d5c74b00940 0x3f1fefc7dc013008 0xa1f8ff7e3ee00980

def z780 : W := mkw 0x970dab8e402a5150 0x84b86d5c7201528a 0x671fc3c7c07ff1fc 0x8338fe1e3e03ff8f

def z781 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0x277fc3c700000000 0x813bfe1e38000000

def z782 : W := mkw 0x150009409280a401 0x00a8004a04940520 0xdf001fc0ff80fe1e 0xfef800fe07fc07f0

def z783 : W := mkw 0x9fcdab8e00000000 0x04fe6d5c70000000 0x3f9fc3c700000000 0xa1fcfe1e38000000

def z784 : W := mkw 0x17042b4c9681ac01 0x00b8215a64b40d60 0xff9e3ffffff1ffff 0xfffcf1ffffff8fff

def z785 : W := mkw 0xa236ffbefb7c001e 0x0511b7fdf7dbe000 0x80003ffffffe001e 0x0c0001fffffff000

def z786 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf003fc0ff81fe12 0xcef801fe07fc0ff0

def z787 : W := mkw 0x4020d0e20186c500 0x22010687100c3628 0xc171d3e7238ece17 0xde0b8e9f391c7670

def z788 : W := mkw 0x9fedbfbe00024100 0x04ff6dfdf0001208 0xffffffff0000c183 0xf7fffffff800060c

def z789 : W := mkw 0x08e990a200000000 0x00474c8510000000 0xa1ffd3e700000003 0xd50ffe9f38000000

def z790 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0xbfffd3c0fffe001f 0xfdfffe9e07fff000

def z791 : W := mkw 0x1516094dbad0a6ad 0x40a8b04a6dd68535 0xb99e1dffc3f0f1f1 0x45ccf0effe1f878f

def z792 : W := mkw 0x17042b4c9681ac01 0x00b8215a64b40d60 0xdf003fffff81fe1e 0xfef801fffffc0ff0

def z793 : W := mkw 0x9dfb9db32c510aac 0x44efdced99628855 0xd961ddc03c710fec 0x4ecb0eee01e3887f

def z794 : W := mkw 0x9fedbfbe00024100 0x04ff6dfdf0001208 0xffffffff007fc1ff 0xf7fffffff803fe0f

def z795 : W := mkw 0x1500004092808400 0x00a8000204940420 0xdf003fc0ff81fe1e 0xfef801fe07fc0ff0

def z796 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3fffc000fffe0011 0xc9fffe0007fff000

def z797 : W := mkw 0x002090e20082c500 0x0001048710041628 0xc171d3e723cecf97 0xde0b8e9f391e767c

def z798 : W := mkw 0x08e094b2402a5150 0x804704a59201528a 0xd8e03fffc07ff1ff 0x76c701fffe03ff8f

def z799 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3fffc000fffe0009 0xa9fffe0007fff000

def z800 : W := mkw 0x0030d0e221c48408 0x00018687110e2420 0xc171d3e723cece17 0xde0b8e9f391e7670

def z801 : W := mkw 0x0020102000024100 0x0001008100001208 0xd8e03c38c07ff1ff 0x76c701e1c603ff8f

def z802 : W := mkw 0x9fedbfbe92000000 0x04ff6dfdf4900000 0xbfffffff3f800003 0xfdfffffff9fc0000

def z803 : W := mkw 0x08e91430402a5150 0x804748a18201528a 0xf8fffc38c07ff1ff 0x77c7ffe1c603ff8f

def z804 : W := mkw 0x3fcd620dd72d0ab2 0x41fe6b106eb96855 0x5961e23fc38f0ff2 0x42cb0f11fe1c787f

def z805 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf001fc0ff80fe16 0xdef800fe07fc07f0

def z806 : W := mkw 0x970daf9e00000000 0x04b86d7cf0000000 0x271fefdf00000000 0x8138ff7ef8000000

def z807 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0xff1fffc7c001f01e 0xf7f8fffe3e000f80

def z808 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbfffffff0031006b 0xf5fffffff8018803

def z809 : W := mkw 0x972dbbae00000000 0x04b96ddd70000000 0x277fc3e700000001 0x813bfe1f38000000

def z810 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbf7fffc700000002 0xf5fbfffe38000000

def z811 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbfffffff23800017 0xfdfffffff91c0000

def z812 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbf7fdfe700000003 0xd5fbfeff38000000

def z813 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf803ff8ff81fe1f 0xfefc01ffc7fc0ff0

def z814 : W := mkw 0x1ddb40002954000c 0x00eeda00014aa000 0x3fffc0003ffe001d 0xf9fffe0001fff000

def z815 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd8803c38c07ff1fe 0x26c401e1c603ff8f

def z816 : W := mkw 0x3fcf2b0cde392837 0x41fe795866f1c941 0x3e8e2c18dc313068 0x21f47160c6e18983

def z817 : W := mkw 0x9fedbfbe04010800 0x04ff6dfdf0200840 0xffffffff3c710fef 0xfffffffff9e3887f

def z818 : W := mkw 0x9ded9dbe00000000 0x04ef6cedf0000000 0xb97fddc700000000 0x45cbfeee38000000

def z819 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xffffffff0001000f 0xf7fffffff8000800

def z820 : W := mkw 0x0204a28e00000000 0x0010251470000000 0x279fe3ff00000003 0xb13cff1ff8000000

def z821 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc171f3e723cfcf9f 0xfe0b8f9f391e7e7c

def z822 : W := mkw 0x8224bffe0483fd41 0x841125fff0241fea 0xc0003fff0001ffe2 0x060001fff8000fff

def z823 : W := mkw 0x9ded9dbe00000000 0x04ef6cedf0000000 0xb9ffdfff00000003 0xd5cffefff8000000

def z824 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0x3fffefff00000001 0xa1ffff7ff8000000

def z825 : W := mkw 0xbfedbfbed2280012 0x05ff6dfdf6914000 0xbfffffffc0000003 0xf5fffffffe000000

def z826 : W := mkw 0x0ae4b6be00000000 0x005725b5f0000000 0xbfffffff00000003 0xf5fffffff8000000

def z827 : W := mkw 0x17042b4c9681ac01 0x00b8215a64b40d60 0xff8e3fd8ff81fe1e 0xfffc71fec7fc0ff0

def z828 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd8e03c38c07ff1f3 0x46c701e1c603ff8f

def z829 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xffffffffc071f1ff 0xf7fffffffe038f8f

def z830 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc171d3e703cecf93 0x460b8e9f381e767c

def z831 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3effc000fffe001d 0x29f7fe0007fff000

def z832 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0x9f003fc0ff81fe18 0xecf801fe07fc0ff0

def z833 : W := mkw 0x9fedbfbed62b7951 0x84ff6dfdf6b15bca 0xffffffffdc7ff1ff 0xf7fffffffee3ff8f

def z834 : W := mkw 0x48f6d4bf697e53fc 0xe247b6a5fb4bf29f 0x20ffc03f007e01e1 0x0107fe01f803f00f

def z835 : W := mkw 0x972dbbae00000000 0x04b96ddd70000000 0xbf7fffe700000003 0xf5fbffff38000000

def z836 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc171d3e7238ecf92 0xce0b8e9f391c767c

def z837 : W := mkw 0x4010c0c321c48688 0x22008606190e2434 0x4171c3e723ce0f97 0xda0b8e1f391e707c

def z838 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x669e023f3c710fed 0x8b34f011f9e3887f

def z839 : W := mkw 0x9de99df2d2aaf551 0x84ef4cef969557aa 0x9961ddc0c38ef010 0x44cb0eee061c7780

def z840 : W := mkw 0x353b5430bb56514e 0x81a9daa185dab28a 0xe71ffc383f81f1e2 0x8f38ffe1c1fc0f8f

def z841 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf803fc0fff1fe1f 0xfefc01fe07ff8ff0

def z842 : W := mkw 0x4020d0e30186c780 0x22010687180c363c 0xc161d3e703cecf97 0x560b0e9f381e767c

def z843 : W := mkw 0x9fcd2f1cd6293851 0x84fe6978e6b149c2 0x3e8e2c18dc313068 0x21f47160c6e18983

def z844 : W := mkw 0x3ddb4001fb7c029e 0x01eeda000fdbe014 0x7fffe23fffff0fff 0xfbffff11fffff87f

def z845 : W := mkw 0x0224b2ae00000000 0x0011259570000000 0xa77fd3e700000003 0xd53bfe9f38000000

def z846 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xd971dfe7e3ceff97 0xdecb8eff3f1e77fc

def z847 : W := mkw 0x3dcb4000db3c0016 0x01ee5a0006d9e000 0x3fffc000dfbe0019 0xf1fffe0006fdf000

def z848 : W := mkw 0x3ddb4410fb7c001e 0x01eeda2087dbe000 0x3fffec18fffe001d 0xf9ffff60c7fff000

def z849 : W := mkw 0x4020d0e30186c780 0x22010687180c363c 0xc161d3e7238ecf96 0xde0b0e9f391c767c

def z850 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0xe69e323f3c71cfff 0xff34f191f9e38e7f

def z851 : W := mkw 0x4032d0e329d6c78c 0x22019687194eb63c 0xe7fff3ff3fffcfff 0xff3fff9ff9fffe7f

def z852 : W := mkw 0x9fedbfbed6293851 0x84ff6dfdf6b149c2 0xbfffffffdc31306b 0xf5fffffffee18983

def z853 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0x9f001fc0ff80fe1c 0xfcf800fe07fc07f0

def z854 : W := mkw 0x0206220d0c110aa4 0x4010311068608855 0x668e223f1c710fef 0x33347111f8e3887f

def z855 : W := mkw 0x8aedbfbe402a5150 0x84576dfdf201528a 0xf8ffffffc07ff1ff 0x77c7fffffe03ff8f

def z856 : W := mkw 0x9fedbfbe40281050 0x84ff6dfdf2014082 0xffffffffc031f07f 0xf7fffffffe018f83

def z857 : W := mkw 0x1fedb2ae00000000 0x00ff6d9570000000 0xbffff3ff00000003 0xf5ffff9ff8000000

def z858 : W := mkw 0x970d2b4c9681ac01 0x04b8695a64b40d60 0xff0e3fc0ff81fe1e 0xfff871fe07fc0ff0

def z859 : W := mkw 0x403290e328d2c78c 0x220194871946963c 0xe69e13e73c70cf8f 0xbf34f09f39e3867c

def z860 : W := mkw 0x9fedbfbe92000000 0x04ff6dfdf4900000 0xffffffffff81f01f 0xfffffffffffc0f80

def z861 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xb9ffffff00000003 0x45cffffff8000000

def z862 : W := mkw 0x4010c0c321c6c788 0x22008606190e363c 0x4171c3c723cecf95 0xda0b8e1e391e767c

def z863 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3fffe018ffff007d 0xf9ffff00c7fff803

def z864 : W := mkw 0x002090a200000000 0x0001048510000000 0xa7ffd3e700000003 0xf53ffe9f38000000

def z865 : W := mkw 0x9fcdaf9e00000000 0x04fe6d7cf0000000 0x279fc3df00000000 0x813cfe1ef8000000

def z866 : W := mkw 0x9fedbfbe96012801 0x04ff6dfdf4b00940 0xbfffffffff81301f 0xfdfffffffffc0980

def z867 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf001fc0ff81fe1c 0xcef800fe07fc0ff0

def z868 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xffffffff0001f003 0xf7fffffff8000f80

def z869 : W := mkw 0x9fedbfbe04010820 0x44ff6dfdf0200841 0xbfffffff00010063 0xf5fffffff8000803

def z870 : W := mkw 0x7de9d4f2d3aed552 0xa3ef4ea7969d76aa 0x9961ddc0c38ef010 0x44cb0eee061c7780

def z871 : W := mkw 0x150009409681ac01 0x00a8004a04b40d60 0xd9001fc0ff81fe1e 0xdec800fe07fc0ff0

def z872 : W := mkw 0x401240416dffdffc 0xe20092020b6ffeff 0x40000000fffffffc 0x0a00000007ffffff

def z873 : W := mkw 0x3ddb4410fb7c105e 0x81eeda2087dbe082 0x3fffcc00fffe301d 0xf9fffe6007fff180

def z874 : W := mkw 0x17042b4c9681ac01 0x00b8215a64b40d60 0xff1e3fc7ff81fe1e 0xfff8f1fe3ffc0ff0

def z875 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0xa71fd3c700000002 0xd538fe9e38000000

def z876 : W := mkw 0x972dbbae00024100 0x04b96ddd70001208 0xe77fd3e7004ec197 0xd73bfe9f3802760c

def z877 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3fffc000dffe0019 0x61fffe0006fff000

def z878 : W := mkw 0x150009409681ac01 0x00a8004a04b40d60 0x99001dc0ff80fe10 0x4cc800ee07fc07f0

def z879 : W := mkw 0x150009409681ac01 0x00a8004a04b40d60 0xdf001dc0ff81fe1c 0xfef800ee07fc0ff0

def z880 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x279fe3df00000000 0xa13cff1ef8000000

def z881 : W := mkw 0x68fbd4b3697e53de 0xa347dea59b4bf29e 0x20ffc03f007e01e1 0x0107fe01f803f00f

def z882 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf803fd8ffb1fe7e 0xfefc01fec7fd8ff3

def z883 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x279fc3ff00000001 0x813cfe1ff8000000

def z884 : W := mkw 0x9fcdaf9e40281050 0x84fe6d7cf2014082 0x3f9fefdfc0313068 0xa1fcff7efe018983

def z885 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x277fc0003f8e0000 0x893bfe0001fc7000

def z886 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x269e023f3c700fed 0xb934f011f9e3807f

def z887 : W := mkw 0x9fcdaf9e00000000 0x04fe6d7cf0000000 0xbf9fffdf00000002 0xf5fcfffef8000000

def z888 : W := mkw 0x9fedbbae00000000 0x04ff6ddd70000000 0xbfffd3e700000003 0xf5fffe9f38000000

def z889 : W := mkw 0x9fedbfbe00024100 0x04ff6dfdf0001208 0xbfffffff000ec013 0xf5fffffff8007600

def z890 : W := mkw 0x0224b2ae00024100 0x0011259570001208 0xe7fff3ff007fc1ff 0xf73fff9ff803fe0f

def z891 : W := mkw 0x9ded94be00000000 0x04ef6ca5f0000000 0xbfffd3ff00000003 0xf5fffe9ff8000000

def z892 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xffffffff007f01ef 0xf7fffffff803f80f

def z893 : W := mkw 0x20124000fb7c001e 0x0100920007dbe000 0x27ffc000fffe001d 0xf93ffe0007fff000

def z894 : W := mkw 0x1509808200000000 0x00a84c0410000000 0x271fc3c700000000 0x8138fe1e38000000

def z895 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbfffffff007001e3 0xf5fffffff803800f

def z896 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x27ffc0003ffe0015 0xd93ffe0001fff000

def z897 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0x27ffc3ff007e01e1 0x813ffe1ff803f00f

def z898 : W := mkw 0x3dcb4000db3c0016 0x01ee5a0006d9e000 0x3f6fc000df8e0010 0x41fb7e0006fc7000

def z899 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x27ffc0003ffe000d 0xb93ffe0001fff000

def z900 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc171d3e723cecf83 0x8e0b8e9f391e767c

def z901 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xffffffff007ec1f7 0xf7fffffff803f60f

def z902 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xffffffff00400187 0xf7fffffff802000c

def z903 : W := mkw 0x9fedbfbe00025140 0x84ff6dfdf000128a 0xbfffffff0000f003 0xf5fffffff8000780

def z904 : W := mkw 0x3ddb4410fb7c105e 0x81eeda2087dbe082 0x3fffc018fffe007d 0xf9fffe00c7fff003

def z905 : W := mkw 0x68f25061fbfec79e 0x234792830fdff63c 0xd8e01020fffecf9f 0x7ec7008107fff67c

def z906 : W := mkw 0x3dcb4000db3c0016 0x01ee5a0006d9e000 0x3fefc000dffe001d 0x71ff7e0006fff000

def z907 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0xbf9fffff00000003 0xf5fcfffff8000000

def z908 : W := mkw 0x9ded9dbe402a5150 0x84ef6cedf201528a 0xf9fffdffc07ff1ff 0x77cfffeffe03ff8f

def z909 : W := mkw 0x4032d0e329d6c7ac 0x62019687194eb63d 0xc171d3e723fecff7 0xde0b8e9f391ff67f

def z910 : W := mkw 0x972dbfbe00000000 0x04b96dfdf0000000 0xa77fffff00000003 0xd53bfffff8000000

def z911 : W := mkw 0x08c00410402a5150 0x804600208201528a 0x58e02c18c07ff1fd 0x72c70160c603ff8f

def z912 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x669e023f3c700fe7 0x9b34f011f9e3807f

def z913 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xde003fc0ff81fe1e 0x2ef001fe07fc0ff0

def z914 : W := mkw 0x970dab8e04010800 0x04b86d5c70200840 0x271fc3c73c000e00 0x8938fe1e39e00070

def z915 : W := mkw 0x9fedbfbe40281050 0x84ff6dfdf2014082 0xbfffffff00300063 0xf5fffffff8018003

def z916 : W := mkw 0x4012404129d6c7ac 0x62009202094eb63d 0x4000000023fecff4 0x0a000000011ff67f

def z917 : W := mkw 0x0016000d285002ac 0x4000b00069428015 0x669e023f3c700fef 0xbb34f011f9e3807f

def z918 : W := mkw 0x60124041fbfc869e 0x230092020fdfe434 0x00000000fffe0e1c 0x0800000007fff070

def z919 : W := mkw 0x5730fba3b7476b89 0x22b987dd1dba3b5c 0x1e71ec27dc4f3189 0x20f38f613ee2798c

def z920 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0x0171c3e723ce0f95 0xd80b8e1f391e707c

def z921 : W := mkw 0x00201430402a5150 0x800100a18201528a 0xd8003c38c07ff1fe 0x76c001e1c603ff8f

def z922 : W := mkw 0x9fedbfbe40281050 0x84ff6dfdf2014082 0xffffffffc07131ef 0xf7fffffffe03898f

def z923 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0xbfffdc00fffef01d 0xfdfffee007fff780

def z924 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0x0171c3c7238e0e00 0x880b8e1e391c7070

def z925 : W := mkw 0x9fcdab8e40280010 0x04fe6d5c72014000 0x3fffc3c7c07e001d 0xf1fffe1e3e03f000

def z926 : W := mkw 0x9fcdab8e00000000 0x04fe6d5c70000000 0x27ffc3c700000001 0x813ffe1e38000000

def z927 : W := mkw 0x401240412dd58eac 0x62009202096eac75 0x400000003ff10fec 0x0a00000001ff887f

def z928 : W := mkw 0x9fedbfbed22a5150 0x84ff6dfdf691528a 0xfffffffffffff1ff 0xffffffffffffff8f

def z929 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xffffffffc031f1eb 0xf7fffffffe018f8f

def z930 : W := mkw 0x4030d4f321c6d7c8 0xa20186a7990e36be 0xd971ffffe3cfffff 0xfecb8fffff1e7fff

def z931 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbf7fffff00000002 0xc5fbfffff8000000

def z932 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc171f3ff23cfcff7 0xde0b8f9ff91e7e7f

def z933 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd8e03e38e07fffff 0xfec701f1c703ffff

def z934 : W := mkw 0x20124041fffdaebf 0x410092020fffed75 0x40000000fffffffc 0x0a00000007ffffff

def z935 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xffffffff007ff1e3 0xf7fffffff803ff8f

def z936 : W := mkw 0x822dbfbe00000000 0x04116dfdf0000000 0xa01fffff00000002 0x0500fffff8000000

def z937 : W := mkw 0x28db4000fb7c001e 0x0146da0007dbe000 0x26ffc000fffe001d 0xb937fe0007fff000

def z938 : W := mkw 0x08e094b2402a5150 0x804704a59201528a 0xd8f1fc3fc07ff1ff 0x76c78fe1fe03ff8f

def z939 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3fffec00ffff301d 0xf9ffff6007fff980

def z940 : W := mkw 0x1de990a2402a4110 0x00ef4c8512015208 0xffffd3e7c07ec19f 0xf7fffe9f3e03f60c

def z941 : W := mkw 0x88ed94be00000000 0x04476ca5f0000000 0xa0ffd3ff00000003 0x0507fe9ff8000000

def z942 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xffffffffc00ff1f3 0xf7fffffffe007f8f

def z943 : W := mkw 0x4032d0e329d6c78c 0x22019687194eb63c 0xc171d3e73ffecf9f 0xde0b8e9f39fff67c

def z944 : W := mkw 0x9fcdab8e00000000 0x04fe6d5c70000000 0xbfffffc700000003 0xf5fffffe38000000

def z945 : W := mkw 0x9ded9dbe00000000 0x04ef6cedf0000000 0xbfffddff00000001 0xf5fffeeff8000000

def z946 : W := mkw 0x9fedbfbe04010800 0x04ff6dfdf0200840 0xfffffffffc01fe1f 0xffffffffffe00ff0

def z947 : W := mkw 0x800d808e00000000 0x04006c0470000000 0x211fc3c700000000 0x8108fe1e38000000

def z948 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xa7ffd3ff00000003 0xd53ffe9ff8000000

def z949 : W := mkw 0x0016000d2c510aac 0x4000b00069628855 0x669e003f3c710fed 0xbb34f001f9e3887f

def z950 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3fffc038fffe01fd 0xf9fffe01c7fff00f

def z951 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd9e03ff8c07ff1ff 0xf6cf01ffc603ff8f

def z952 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xd9f1ffffe3ffffff 0xfecf8fffff1fffff

def z953 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0x3fffc3ff00000001 0xf1fffe1ff8000000

def z954 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0x8171d3e7238ece13 0xdc0b8e9f391c7670

def z955 : W := mkw 0x4224b6ff0483dfe0 0xe21125b7f8241eff 0xc0003fff0001ffe2 0x060001fff8000fff

def z956 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf103fe7ff81fe1f 0xfef881ff3ffc0ff0

def z957 : W := mkw 0x0204a28e00000000 0x0010251470000000 0x271fc3c700000000 0x8138fe1e38000000

def z958 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc161d3e723cecf96 0x4e0b0e9f391e767c

def z959 : W := mkw 0xbfcf2f1cde390836 0x45fe7978e6f1c841 0x3e8e2c18dc310068 0x21f47160c6e18803

def z960 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0x8171d3e723cecf91 0xcc0b8e9f391e767c

def z961 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbfffffff0070000f 0xf5fffffff8038000

def z962 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xdee03c38fc7ff1ff 0xfef701e1c7e3ff8f

def z963 : W := mkw 0xbfcf2f1cde392817 0x05fe7978e6f1c940 0x3e8e2c18dc313008 0x21f47160c6e18980

def z964 : W := mkw 0x972dbbae00000000 0x04b96ddd70000000 0xa7fff3ff00000003 0xf53fff9ff8000000

def z965 : W := mkw 0x1de994b200000000 0x00ef4ca590000000 0xbfffffff00000003 0xf5fffffff8000000

def z966 : W := mkw 0x0206220d0c110aa4 0x4010311068608855 0x669e223f1c310feb 0xb334f111f8e1887f

def z967 : W := mkw 0x15124000bb54000c 0x00a8920005daa000 0x3fffc000fffe001d 0xf9fffe0007fff000

def z968 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xbfffffff000e0003 0xf5fffffff8007000

def z969 : W := mkw 0x9fedbfbe92000000 0x04ff6dfdf4900000 0xbfffffffdc00000b 0xf5fffffffee00000

def z970 : W := mkw 0x1fcd2b0c00000000 0x00fe695860000000 0xbfffffff00000003 0xf5fffffff8000000

def z971 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbffffdff00000001 0x65ffffeff8000000

def z972 : W := mkw 0x3dc94000d32c0012 0x01ee4a0006996000 0x3fffc000ff8e001d 0xf9fffe0007fc7000

def z973 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x269e223f3c710fe9 0xa934f111f9e3887f

def z974 : W := mkw 0x0216620d2d550aac 0x4010b310696aa855 0x679fe23f3ff10fef 0xbb3cff11f9ff887f

def z975 : W := mkw 0x970dab8e92000000 0x04b86d5c74900000 0x3f1fc3c7ff80001c 0xf9f8fe1e3ffc0000

def z976 : W := mkw 0x0206220d0c110aa4 0x4010311068608855 0x668e223f3c310fee 0xbb347111f9e1887f

def z977 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0x4171c3e723cecf95 0x8a0b8e1f391e767c

def z978 : W := mkw 0x351b4000bb54000e 0x01a8da0005daa000 0x3f7fc000ffce001d 0xf9fbfe0007fe7000

def z979 : W := mkw 0x1de994b2402a5150 0x80ef4ca59201528a 0xffffffffc07ff1ff 0xf7fffffffe03ff8f

def z980 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3f7fc000ff8e001c 0xf9fbfe0007fc7000

def z981 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbfffffffc000001f 0xf5fffffffe000000

def z982 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd9f1fc38c07ff1ff 0xf6cf8fe1c603ff8f

def z983 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc1f1d3e723fecf9f 0xfe0f8e9f391ff67c

def z984 : W := mkw 0x08d24000697c001c 0x00469200034be000 0x3fffc000fffe001d 0xf9fffe0007fff000

def z985 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x271fc3e700000003 0x9138fe1f38000000

def z986 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc771d3e73fcecf9f 0xfe3b8e9f39fe767c

def z987 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x3f1fc3c700000000 0xf1f8fe1e38000000

def z988 : W := mkw 0x351b4000bb54000e 0x01a8da0005daa000 0x277fc0003fce0001 0x893bfe0001fe7000

def z989 : W := mkw 0x0ae4b6be402a5150 0x805725b5f201528a 0xffffffffc07ff1ff 0xf7fffffffe03ff8f

def z990 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x27ffc000fffe001d 0x893ffe0007fff000

def z991 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbfffffff004e0017 0xf5fffffff8027000

def z992 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbf9fffff00000002 0xa5fcfffff8000000

def z993 : W := mkw 0x0216620d2d550aac 0x4010b310696aa855 0x669e223f3fff0fff 0xbb34f111f9fff87f

def z994 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xff9e3fc0ff81fe1f 0xfffcf1fe07fc0ff0

def z995 : W := mkw 0x8aedbfbe00000000 0x04576dfdf0000000 0xa6ffffff00000003 0xb537fffff8000000

def z996 : W := mkw 0x9fcdaf9e00000000 0x04fe6d7cf0000000 0x3f9fefff00000003 0xb1fcff7ff8000000

def z997 : W := mkw 0x8224bfbe00000000 0x041125fdf0000000 0xa7ffffff00000003 0xf53ffffff8000000

def z998 : W := mkw 0x3ddb4000fb7c105e 0x81eeda0007dbe082 0x3fffc000ffff307d 0xf9fffe0007fff983

def z999 : W := mkw 0x88ed9dbe00000000 0x04476cedf0000000 0xa0ffddff00000001 0x0507feeff8000000

def z1000 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd8e03c18c07ff1fc 0x66c701e0c603ff8f

def z1001 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x7fffc000fffff01d 0xfbfffe0007ffff80

def z1002 : W := mkw 0x02162b0d2c510aac 0x4010b15869628855 0xe69e3fff3c710fef 0xbf34f1fff9e3887f

def z1003 : W := mkw 0x9fedbfbe04010800 0x04ff6dfdf0200840 0xbfffffff1c01000b 0xf5fffffff8e00800

def z1004 : W := mkw 0x9fcdab8e00000000 0x04fe6d5c70000000 0x3fffe3ff00000003 0xf1ffff1ff8000000

def z1005 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x7e9e2e3ffc713fef 0xbbf4f171ffe389ff

def z1006 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xd971ffe723cecf97 0xfecb8fff391e767c

def z1007 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc171ffe723cfff97 0xde0b8fff391e7ffc

def z1008 : W := mkw 0x9fedbfbe00024100 0x04ff6dfdf0001208 0xffffffffc04ff19f 0xf7fffffffe027f8c

def z1009 : W := mkw 0x08c00410402a5150 0x804600208201528a 0xd8803c18c07ff1fe 0x76c401e0c603ff8f

def z1010 : W := mkw 0x0010404121c48688 0x00008202090e2434 0xc171d3e723cecf97 0xde0b8e9f391e767c

def z1011 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbfffdfc700000001 0xf5fffefe38000000

def z1012 : W := mkw 0x1dc9808200000000 0x00ee4c0410000000 0x3fffc3c700000001 0xf1fffe1e38000000

def z1013 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc171d3c7238ece16 0xde0b8e9e391c7670

def z1014 : W := mkw 0x9fedbfbe04010800 0x04ff6dfdf0200840 0xbfffffff3c000e03 0xfdfffffff9e00070

def z1015 : W := mkw 0x9de99db200000000 0x04ef4ced90000000 0xbfffdfe700000003 0xf5fffeff38000000

def z1016 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbfffdfff00000001 0xc5fffefff8000000

def z1017 : W := mkw 0x3ddb4001fb7c029e 0x01eeda000fdbe014 0x3fffc027fffe019d 0xf9fffe013ffff00c

def z1018 : W := mkw 0x9fedbfbe40280010 0x04ff6dfdf2014000 0xffffffffc07f01ff 0xf7fffffffe03f80f

def z1019 : W := mkw 0x3ddb4001fb7c029e 0x01eeda000fdbe014 0x7fffc000fffe0f9d 0xfbfffe0007fff07c

def z1020 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xbfffffffc03ff07b 0xf5fffffffe01ff83

def z1021 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbfffffffc001300b 0xf5fffffffe000980

def z1022 : W := mkw 0x970dab8e04010800 0x04b86d5c70200840 0x671fe3c73c010e0e 0xbb38ff1e39e00870

def z1023 : W := mkw 0x002490ae00000000 0x0001248570000000 0xa1ffd3ff00000003 0xd50ffe9ff8000000

def z1024 : W := mkw 0x9fcdaf9e00000000 0x04fe6d7cf0000000 0x3fffefdf00000001 0xf1ffff7ef8000000

def z1025 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc171d3c723cecf94 0xce0b8e9e391e767c

def z1026 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xffffffffc00ff01f 0xf7fffffffe007f80

def z1027 : W := mkw 0x4010c0c321c48688 0x22008606190e2434 0x0171c3c7238e0e10 0xc80b8e1e391c7070

def z1028 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0xbffffc00fffe001f 0xfdffffe007fff000

def z1029 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbfffffffc000f013 0xf5fffffffe000780

def z1030 : W := mkw 0x3ddb4001fb7c02be 0x41eeda000fdbe015 0x3fffc000fffe01fd 0xf9fffe0007fff00f

def z1031 : W := mkw 0x4020d0e30186c780 0x22010687180c363c 0x8161d3c7038ece10 0x440b0e9e381c7670

def z1032 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x669e223f1c710feb 0x2334f111f8e3887f

def z1033 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3fffc000ffbe0018 0xe9fffe0007fdf000

def z1034 : W := mkw 0x9fcdaf9e00000000 0x04fe6d7cf0000000 0x3f1fcfc700000000 0x81f8fe7e38000000

def z1035 : W := mkw 0x970dab8e96012801 0x04b86d5c74b00940 0x271fc3c71c000000 0x8138fe1e38e00000

def z1036 : W := mkw 0x4030d4f321c6d7c8 0xa20186a7990e36be 0xc171dfe723ceff97 0xde0b8eff391e77fc

def z1037 : W := mkw 0x403250612dd7cfac 0x62019283096ebe7d 0xc0e030383fffcfff 0x7e070181c1fffe7f

def z1038 : W := mkw 0x001240002954000c 0x00009200014aa000 0x277fc0003fce0015 0xd93bfe0001fe7000

def z1039 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf003fc0ff81fe0a 0xaef801fe07fc0ff0

def z1040 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0xd8e03c38c07ff1eb 0x26c701e1c603ff8f

def z1041 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf003fe0ffc1ff9f 0xfef801ff07fe0ffc

def z1042 : W := mkw 0x150009409681ac01 0x00a8004a04b40d60 0xd9003dc0ff81fe1e 0x7ec801ee07fc0ff0

def z1043 : W := mkw 0x02002b409681ac01 0x0010015a04b40d60 0xd8003fc0ff81fe1e 0x7ec001fe07fc0ff0

def z1044 : W := mkw 0x88ed94be00000000 0x04476ca5f0000000 0x21ffc3ff00000001 0x810ffe1ff8000000

def z1045 : W := mkw 0x9fcdab8e00000000 0x04fe6d5c70000000 0x3f7fc3c700000000 0xc1fbfe1e38000000

def z1046 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x668e223f3c710fee 0x2b347111f9e3887f

def z1047 : W := mkw 0x4224bbef0483efa1 0x621125df78241f7d 0xc0003fff0001ffe2 0x060001fff8000fff

def z1048 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x679fe3ff007101ef 0xb33cff1ff803880f

def z1049 : W := mkw 0x60124041bbd6c78e 0x230092020ddeb63c 0x400000003fcecf94 0x0a00000001fe767c

def z1050 : W := mkw 0x08c0000040280010 0x0046000002014000 0xd8e03c38c07ff1ff 0x76c701e1c603ff8f

def z1051 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0xbf1fdfc700000000 0xc5f8fefe38000000

def z1052 : W := mkw 0x0216620d2d550aac 0x4010b310696aa855 0x66ffe23f3c7f0fef 0xbb37ff11f9e3f87f

def z1053 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xffffffff000101e3 0xf7fffffff800080f

def z1054 : W := mkw 0x88e994b2402a5150 0x84474ca59201528a 0xd8e1fc38c07ff1ff 0x76c70fe1c603ff8f

def z1055 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf603fc0ffcffe1f 0xfefb01fe07fe7ff0

def z1056 : W := mkw 0x0214620d25450aa8 0x4010a310692a2855 0x4171e23f23cf0ff7 0xda0b8f11f91e787f

def z1057 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x669e223f3c310fea 0xab34f111f9e1887f

def z1058 : W := mkw 0x3dcb4000db3c0016 0x01ee5a0006d9e000 0x3fefc000ffbe001c 0xf9ff7e0007fdf000

def z1059 : W := mkw 0x60124041bbd4868e 0x230092020ddea434 0x000000003f800e00 0x0800000001fc0070

def z1060 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xbfffffffc07e01ff 0xf5fffffffe03f00f

def z1061 : W := mkw 0x88ed94be00000000 0x04476ca5f0000000 0xb9ffffff00000003 0xf5cffffff8000000

def z1062 : W := mkw 0x3ddb4900fb7c201f 0x01eeda4807dbe100 0x3fffcc00fffe301d 0xf9fffe6007fff180

def z1063 : W := mkw 0x4012404129d6c78c 0x22009202094eb63c 0x400000003ffecf9c 0x0a00000001fff67c

def z1064 : W := mkw 0x4030d4f321c6d7c8 0xa20186a7990e36be 0xc171d3ff23cecff7 0xde0b8e9ff91e767f

def z1065 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3fffc000ff8e0011 0xf9fffe0007fc7000

def z1066 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0x27ffe3ff00000003 0xb13fff1ff8000000

def z1067 : W := mkw 0x4010c0c321c48688 0x22008606190e2434 0xc171d3c723cece17 0xde0b8e9e391e7670

def z1068 : W := mkw 0x9fedbfbe00024100 0x04ff6dfdf0001208 0xbfffffff004e0183 0xf5fffffff802700c

def z1069 : W := mkw 0x9fedbfbe402a4110 0x04ff6dfdf2015208 0xffffffffc07ec19f 0xf7fffffffe03f60c

def z1070 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf003ff8ff81fffe 0xfef801ffc7fc0fff

def z1071 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xd971d3e7e3cecf9f 0xfecb8e9f3f1e767c

def z1072 : W := mkw 0x972dbfbe00000000 0x04b96dfdf0000000 0xa79fffff00000003 0xb53cfffff8000000

def z1073 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc171d3e7e3cfff9f 0xde0b8e9f3f1e7ffc

def z1074 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0xffffd000fffec01f 0xfffffe8007fff600

def z1075 : W := mkw 0x9fedbfbe40280010 0x04ff6dfdf2014000 0xbfffffffc030000b 0xf5fffffffe018000

def z1076 : W := mkw 0x4010c0c321c48688 0x22008606190e2434 0x0171c3c723ce0e01 0x880b8e1e391e7070

def z1077 : W := mkw 0x9fedbfbe00025140 0x84ff6dfdf000128a 0xbfffffff000001e3 0xf5fffffff800000f

def z1078 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0x9f003fc0ff80fe12 0xfcf801fe07fc07f0

def z1079 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3fefc000fffe001c 0x69ff7e0007fff000

def z1080 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xbfffffffc07f31eb 0xf5fffffffe03f98f

def z1081 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x7fffc020fffe019f 0xfbfffe0107fff00c

def z1082 : W := mkw 0x972dbbae00000000 0x04b96ddd70000000 0xa71fd3e700000002 0x8538fe9f38000000

def z1083 : W := mkw 0x000000409681ac01 0x0000000204b40d60 0xd9003fc0ff81fe1e 0xfec801fe07fc0ff0

def z1084 : W := mkw 0x3ddb4000bb54000e 0x01eeda0005daa000 0x3fffc0003fce0015 0xf9fffe0001fe7000

def z1085 : W := mkw 0x8aedbfbe402a5150 0x84576dfdf201528a 0xe0ffffff007ff1e3 0x0707fffff803ff8f

def z1086 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc1f1d3ff23fecff7 0xde0f8e9ff91ff67f

def z1087 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x271fe3c700000002 0xb138ff1e38000000

def z1088 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xbfffffffc07ef1f3 0xf5fffffffe03f78f

def z1089 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbfffffff3c00000f 0xfdfffffff9e00000

def z1090 : W := mkw 0x1fe9bba200000000 0x00ff4ddd10000000 0xbfffffe700000003 0xf5ffffff38000000

def z1091 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf003fc0fff1fffe 0xfef801fe07ff8fff

def z1092 : W := mkw 0x950d898e00000000 0x04a86c4c70000000 0x211fc1c700000000 0x0108fe0e38000000

def z1093 : W := mkw 0x0030d0a321440288 0x00018685190a2014 0xc171d3e723ce0f97 0xde0b8e9f391e707c

def z1094 : W := mkw 0x9ded9dbe402a5150 0x84ef6cedf201528a 0xb9ffddffc07ef1f1 0x45cffeeffe03f78f

def z1095 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x271fe3ff00000002 0x8138ff1ff8000000

def z1096 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x679e223f3ff10fff 0xfb3cf111f9ff887f

def z1097 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x7fffe000ffff001f 0xfbffff0007fff800

def z1098 : W := mkw 0x9fedbfbe40280010 0x04ff6dfdf2014000 0xbfffffffc00e0013 0xf5fffffffe007000

def z1099 : W := mkw 0x5716ebcfbfd5aead 0x62b8b75e7dfead75 0x271fc3c73f800e00 0x8938fe1e39fc0070

def z1100 : W := mkw 0x9fedbfbe402a5150 0x84ff6dfdf201528a 0xffffffffc04ef197 0xf7fffffffe02778c

def z1101 : W := mkw 0x40124041bfd7efad 0x620092020dfebf7d 0x40000000fffffffc 0x0a00000007ffffff

def z1102 : W := mkw 0x351b4000bb54000e 0x01a8da0005daa000 0x277fc0003f8e0010 0xc93bfe0001fc7000

def z1103 : W := mkw 0x3ddb4001fb7c029e 0x01eeda000fdbe014 0x3fffc207fffe0e1d 0xf9fffe103ffff070

def z1104 : W := mkw 0x972dbfbe00000000 0x04b96dfdf0000000 0xa71fdfc700000000 0x8538fefe38000000

def z1105 : W := mkw 0xbddb4d10fb7c001e 0x05eeda6887dbe000 0x3fffcc00fffe001d 0xf9fffe6007fff000

def z1106 : W := mkw 0x88ed94be402a5150 0x84476ca5f201528a 0xe1ffd3ff007ec1f7 0xd70ffe9ff803f60f

def z1107 : W := mkw 0x9fedbfbe92000000 0x04ff6dfdf4900000 0xbfffffffc3800013 0xf5fffffffe1c0000

def z1108 : W := mkw 0x02162b0d2c512aad 0x4010b15869628955 0x669e2e3f3c713fef 0xbb34f171f9e389ff

def z1109 : W := mkw 0x4224b2ef0483cfa0 0x6211259778241e7d 0xc00013e70000cf82 0x0600009f3800067c

def z1110 : W := mkw 0x17042b4c9681ac21 0x40b8215a64b40d61 0xdf003fd8ff81fe7e 0xfef801fec7fc0ff3

def z1111 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0xe69e3e3f3c71ffef 0xbf34f1f1f9e38fff

def z1112 : W := mkw 0x972dbbae00000000 0x04b96ddd70000000 0xa77fd3c700000000 0xc53bfe9e38000000

def z1113 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0xe79e33ff3c710fef 0xff3cf19ff9e3887f

def z1114 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x669e223f3c710fe3 0x8b34f111f9e3887f

def z1115 : W := mkw 0x351b4000bb54000e 0x01a8da0005daa000 0x27ffc0003ffe001d 0xf93ffe0001fff000

def z1116 : W := mkw 0x9fedbfbe40281050 0x84ff6dfdf2014082 0xbfffffffc0003003 0xf5fffffffe000180

def z1117 : W := mkw 0x401240412dd58eac 0x62009202096eac75 0x000000003f800e00 0x0800000001fc0070

def z1118 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0x98e03c38c07ff1f9 0x64c701e1c603ff8f

def z1119 : W := mkw 0x970dab8e92000000 0x04b86d5c74900000 0x271fc3c73f800000 0x8938fe1e39fc0000

def z1120 : W := mkw 0x9fedbfbe00025140 0x84ff6dfdf000128a 0xffffffff0071f1ef 0xf7fffffff8038f8f

def z1121 : W := mkw 0x970dab8e00000000 0x04b86d5c70000000 0x277fc3c700000001 0xd13bfe1e38000000

def z1122 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xa7ffffff00000003 0x853ffffff8000000

def z1123 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3fffc0003ffe0001 0xf9fffe0001fff000

def z1124 : W := mkw 0x9fedbfbe40281050 0x84ff6dfdf2014082 0xbfffffffc07f307f 0xf5fffffffe03f983

def z1125 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbfffffdf00000000 0xe5fffffef8000000

def z1126 : W := mkw 0x3ddb4900fb7c001e 0x01eeda4807dbe000 0xbfffddc0fffe001d 0xfdfffeee07fff000

def z1127 : W := mkw 0x4020d0e30186c780 0x22010687180c363c 0xc171d3e7038ecf93 0xd60b8e9f381c767c

def z1128 : W := mkw 0x8aedbfbe00000000 0x04576dfdf0000000 0xa1ffffff00000003 0xd50ffffff8000000

def z1129 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xd9003fc0ff81fe1e 0x4ec801fe07fc0ff0

def z1130 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0xfe9e3e3f3c710fef 0xfff4f1f1f9e3887f

def z1131 : W := mkw 0x8aedbfbe00000000 0x04576dfdf0000000 0x20ffc3ff00000001 0x0107fe1ff8000000

def z1132 : W := mkw 0x3ddb4410fb7c105e 0x81eeda2087dbe082 0xfffffc18fffff07f 0xffffffe0c7ffff83

def z1133 : W := mkw 0x4030d0e321c48688 0x22018687190e2434 0x8171d3e723ce0e17 0xdc0b8e9f391e7070

def z1134 : W := mkw 0x08e01430402a5150 0x804700a18201528a 0x58e02c38c07ff1fd 0x22c70161c603ff8f

def z1135 : W := mkw 0x9fedbfbe442b5950 0x84ff6dfdf2215aca 0xfffffffffc7fffff 0xffffffffffe3ffff

def z1136 : W := mkw 0x1724bbae00000000 0x00b925dd70000000 0xbfffffff00000003 0xf5fffffff8000000

def z1137 : W := mkw 0x3ddb4410fb7c105e 0x81eeda2087dbe082 0x7fffec38ffff31ff 0xfbffff61c7fff98f

def z1138 : W := mkw 0x9fedbfbe96012801 0x04ff6dfdf4b00940 0xbfffffff1c000003 0xf5fffffff8e00000

def z1139 : W := mkw 0x152990a200000000 0x00a94c8510000000 0xa77fd3e700000003 0xd53bfe9f38000000

def z1140 : W := mkw 0x9fedbfbe00025140 0x84ff6dfdf000128a 0xffffffffc001f1ff 0xf7fffffffe000f8f

def z1141 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf003dc0ff81fe1c 0x6ef801ee07fc0ff0

def z1142 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xffffffff0000c017 0xf7fffffff8000600

def z1143 : W := mkw 0x371f6b4dbfd5aeaf 0x41b8fb5a6dfead75 0x271fc3c73f800e00 0x8938fe1e39fc0070

def z1144 : W := mkw 0x08c00410402a5150 0x804600208201528a 0x58802c38c07ff1ff 0x32c40161c603ff8f

def z1145 : W := mkw 0x3ddb4000fb7c001e 0x01eeda0007dbe000 0x3f7fc000fffe001c 0xc9fbfe0007fff000

def z1146 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xffffffff20000e07 0xfffffffff9000070

def z1147 : W := mkw 0x9fedbfbe40280010 0x04ff6dfdf2014000 0xffffffffc07ff01f 0xf7fffffffe03ff80

def z1148 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0x8171d3e723ce0f83 0xdc0b8e9f391e707c

def z1149 : W := mkw 0x17002b409681ac01 0x00b8015a04b40d60 0xdf71ffc0ff81fe1f 0xfefb8ffe07fc0ff0

def z1150 : W := mkw 0x9fedbfbe00025140 0x84ff6dfdf000128a 0xffffffff004ff1f7 0xf7fffffff8027f8f

def z1151 : W := mkw 0x0216220d2c510aac 0x4010b11069628855 0x669e223ffc71ffff 0xbb34f111ffe38fff

def z1152 : W := mkw 0x4032d0e329d6c78c 0x22019687194eb63c 0xe1ffd3e723fecf97 0xdf0ffe9f391ff67c

def z1153 : W := mkw 0x4032d0e329d6c78c 0x22019687194eb63c 0xe77fd3e73fcecf97 0xdf3bfe9f39fe767c

def z1154 : W := mkw 0x9fedbfbe96010800 0x04ff6dfdf4b00840 0xffffffffff810e1f 0xfffffffffffc0870

def z1155 : W := mkw 0x4030d0e321c6c788 0x22018687190e363c 0xc1f1f3ff23cecf97 0xfe0f8f9ff91e767c

def z1156 : W := mkw 0x08e094b2402a5150 0x804704a59201528a 0xd9e1fdf8c07ff1ff 0x76cf0fefc603ff8f

def z1157 : W := mkw 0x9fedbfbe00000000 0x04ff6dfdf0000000 0xbeffffff00000003 0x25f7fffff8000000

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z0,z1,z2,z3,z4,z7,z8]),(0,[z9,z0,z1,z2,z3,z4,z10])],[(0,[z11,z0,z1,z2,z3,z4,z5]),(0,[z12,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z13,z4,z5]),(0,[z14,z1,z2,z15,z3,z4,z5]),(0,[z0,z1,z2,z16,z3,z4,z5]),(0,[z17,z0,z1,z2,z18,z4,z5]),(0,[z19,z0,z1,z2,z20,z4,z5]),(0,[z21,z0,z1,z2,z3,z4,z5]),(0,[z22,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z1,z2,z3,z4,z10]),(0,[z0,z1,z23,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z24,z5]),(0,[z0,z1,z2,z3,z4,z5,z25])],[(0,[z26,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z27,z28,z5]),(0,[z0,z1,z2,z3,z4,z29,z5])],[(0,[z0,z1,z2,z3,z4,z30,z5]),(0,[z0,z1,z2,z3,z31,z4,z5]),(0,[z32,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z33,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z34,z5])],[(0,[z35,z0,z1,z2,z3,z4,z5]),(0,[z36,z0,z1,z2,z37,z4,z5]),(0,[z0,z1,z2,z38,z3,z4,z5]),(0,[z32,z0,z1,z3,z4,z39,z5]),(0,[z0,z40,z1,z2,z3,z4,z5])],[(0,[z41,z0,z1,z2,z3,z4,z10])],[(0,[z42,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z43,z5]),(0,[z0,z44,z1,z45,z3,z4,z5]),(0,[z0,z1,z2,z46,z3,z4,z5]),(0,[z47,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z48,z3,z4,z5])]],
   [[(0,[z49,z0,z1,z2,z3,z4,z5]),(0,[z0,z50,z1,z2,z3,z51,z5]),(0,[z0,z1,z2,z52,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z53,z5])],[(0,[z54,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z55,z4,z10]),(0,[z0,z1,z2,z56,z3,z4,z5]),(0,[z0,z1,z57,z2,z3,z4,z58])],[(0,[z0,z1,z59,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z60,z8])],[(0,[z0,z1,z2,z3,z4,z5,z61]),(0,[z0,z44,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z63,z3,z4,z5]),(0,[z0,z1,z2,z3,z64,z4,z8]),(0,[z0,z1,z2,z3,z65,z4,z8]),(0,[z0,z1,z2,z3,z4,z66,z5]),(0,[z0,z1,z67,z2,z3,z4,z5])],[(0,[z0,z1,z68,z2,z3,z4,z5]),(0,[z0,z1,z69,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z70,z4,z5]),(0,[z71,z0,z1,z2,z3,z4,z5]),(0,[z72,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z73,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z74]),(0,[z75,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z76,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z77])],[(0,[z0,z1,z2,z3,z78,z4,z5]),(0,[z79,z0,z1,z2,z3,z4,z5])],[(0,[z80,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z81,z5]),(0,[z0,z1,z2,z82,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z83,z5]),(0,[z0,z1,z2,z3,z4,z84,z5])],[(1,[z0,z1,z2,z3,z4,z85]),(0,[z0,z1,z2,z3,z4,z5,z86]),(0,[z0,z1,z2,z3,z87,z4,z5]),(1,[z0,z1,z2,z3,z88,z5]),(0,[z36,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z89,z3,z4,z5]),(0,[z90,z0,z1,z2,z3,z4,z91]),(0,[z92,z0,z1,z2,z3,z4,z5]),(0,[z36,z0,z1,z2,z93,z4,z5])],[(0,[z94,z0,z1,z95,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z96]),(0,[z0,z1,z2,z3,z4,z97,z5])],[(0,[z94,z0,z1,z2,z3,z98,z5]),(0,[z94,z0,z1,z2,z3,z4,z8]),(0,[z99,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z100,z5]),(0,[z0,z1,z101,z2,z3,z39,z5])],[(0,[z0,z1,z2,z3,z4,z102,z5]),(0,[z0,z1,z2,z3,z4,z103,z5]),(1,[z9,z0,z1,z2,z28,z5]),(0,[z0,z1,z2,z3,z4,z104,z5]),(0,[z0,z1,z2,z3,z4,z5,z105])],[(0,[z0,z50,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z5,z8])],[(0,[z106,z0,z107,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z108,z4,z5]),(0,[z109,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z110,z5]),(0,[z111,z0,z1,z2,z3,z4,z5])],[(0,[z112,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z70,z4,z28,z5]),(0,[z113,z0,z1,z2,z3,z4,z114])],[(0,[z115,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z116,z5]),(0,[z0,z1,z2,z3,z117,z4,z5]),(0,[z0,z1,z2,z3,z118,z4,z5]),(0,[z119,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z37,z4,z8]),(0,[z0,z1,z2,z3,z4,z120,z5])]],
   [[(1,[z17,z1,z2,z18,z4,z5]),(0,[z0,z1,z2,z121,z3,z4,z5]),(0,[z90,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z10,z5]),(0,[z0,z1,z2,z3,z4,z122,z5]),(0,[z109,z0,z1,z2,z3,z4,z10]),(0,[z123,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z124,z76,z4,z5])],[(0,[z125,z0,z1,z2,z3,z4,z5]),(0,[z126,z0,z1,z2,z127,z4,z5]),(0,[z0,z1,z2,z3,z4,z128,z5]),(0,[z129,z0,z1,z2,z3,z4,z5])],[(0,[z0,z130,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z131,z3,z4,z5]),(0,[z0,z132,z1,z2,z3,z4,z74]),(0,[z0,z1,z2,z133,z3,z4,z5])],[],[(0,[z0,z134,z1,z2,z3,z4,z5]),(0,[z0,z135,z2,z3,z4,z5,z8])],[(0,[z0,z1,z2,z136,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z137,z138]),(0,[z0,z1,z3,z4,z58,z5,z137])],[(0,[z0,z1,z2,z3,z139,z4,z5]),(0,[z0,z140,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z141]),(0,[z32,z0,z1,z2,z3,z39,z5]),(0,[z0,z1,z2,z3,z4,z142,z5]),(0,[z0,z1,z2,z143,z3,z4,z5]),(0,[z144,z0,z1,z2,z143,z3,z4])]],
   [[(0,[z145,z0,z1,z2,z3,z4,z8]),(0,[z126,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z51,z8]),(0,[z0,z1,z2,z146,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z58,z77])],[(1,[z14,z1,z15,z3,z4,z5]),(0,[z0,z1,z2,z147,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z148,z5]),(0,[z149,z0,z1,z2,z3,z4,z5]),(0,[z150,z0,z1,z2,z3,z4,z8]),(0,[z126,z0,z1,z2,z151,z4,z5]),(0,[z152,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z10])],[(0,[z0,z153,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z70,z4,z154,z5]),(0,[z0,z1,z2,z3,z4,z155,z5]),(1,[z0,z1,z2,z156,z4,z5]),(0,[z0,z1,z2,z3,z151,z4,z8]),(0,[z0,z1,z2,z3,z157,z4,z5])],[(0,[z0,z1,z2,z3,z4,z4,z5]),(0,[z0,z1,z158,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z159,z4,z5]),(0,[z0,z1,z2,z143,z3,z4,z8]),(0,[z0,z1,z2,z124,z3,z28,z5]),(0,[z0,z1,z2,z143,z3,z160,z4]),(0,[z0,z1,z2,z161,z3,z4,z5]),(0,[z0,z1,z2,z3,z162,z5,z163]),(0,[z0,z1,z2,z3,z4,z164,z5])],[(0,[z0,z1,z2,z3,z4,z165,z5]),(0,[z19,z0,z1,z2,z3,z88,z5]),(0,[z0,z166,z2,z45,z3,z4,z5]),(0,[z167,z0,z1,z2,z3,z4,z5])],[(0,[z168,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z169,z4,z5]),(0,[z0,z50,z2,z3,z4,z5,z8]),(0,[z0,z1,z2,z3,z170,z4,z5]),(0,[z144,z0,z1,z2,z3,z4,z58])],[(0,[z0,z1,z2,z171,z3,z4,z5]),(0,[z9,z17,z0,z1,z2,z4,z5]),(0,[z0,z132,z1,z2,z127,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z172]),(0,[z0,z1,z173,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z174,z2,z3,z4,z5]),(0,[z17,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z175,z5]),(1,[z0,z1,z2,z3,z4,z176]),(0,[z0,z1,z2,z177,z3,z4,z5]),(0,[z0,z1,z2,z3,z178,z4,z5]),(0,[z0,z1,z2,z3,z4,z179,z5]),(0,[z9,z0,z1,z2,z124,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z180]),(0,[z0,z1,z2,z3,z181,z4,z5]),(0,[z0,z182,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z183,z5])],[(0,[z0,z1,z184,z2,z3,z4,z5]),(0,[z185,z1,z2,z3,z70,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z186]),(0,[z0,z1,z2,z3,z4,z114,z8]),(0,[z0,z1,z2,z3,z51,z39,z5]),(0,[z0,z187,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z188,z5]),(0,[z0,z1,z2,z3,z4,z162,z8]),(0,[z0,z1,z2,z3,z189,z4,z5]),(1,[z0,z1,z2,z3,z4,z190])],[(0,[z0,z1,z2,z3,z191,z4,z5]),(0,[z0,z1,z2,z3,z192,z4,z5]),(0,[z0,z1,z2,z193,z3,z4,z5]),(0,[z150,z0,z1,z2,z194,z4,z5]),(0,[z0,z195,z1,z2,z3,z4,z5]),(0,[z196,z0,z1,z2,z3,z4,z5])],[(0,[z0,z197,z1,z2,z3,z4,z5]),(0,[z113,z0,z1,z198,z3,z4,z5]),(0,[z0,z1,z2,z177,z3,z4,z8]),(0,[z199,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z200,z5]),(0,[z0,z1,z201,z2,z3,z4,z5]),(0,[z0,z132,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z160,z4,z8]),(0,[z0,z1,z2,z3,z4,z202,z5])],[(0,[z0,z1,z107,z2,z3,z4,z10]),(1,[z0,z1,z2,z3,z203,z5]),(0,[z0,z1,z2,z3,z204,z4,z5]),(0,[z205,z0,z1,z2,z3,z4,z5]),(0,[z196,z0,z1,z2,z3,z4,z10]),(0,[z0,z206,z1,z2,z3,z4,z5])]],
   [[(0,[z106,z0,z1,z2,z3,z4,z8]),(0,[z14,z0,z1,z15,z3,z4,z5]),(0,[z0,z1,z207,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z208]),(0,[z209,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z210,z4,z8]),(0,[z211,z0,z2,z3,z4,z10,z5]),(0,[z0,z1,z2,z212,z3,z4,z5])],[(0,[z113,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z213,z2,z3,z4,z5]),(0,[z0,z1,z2,z214,z3,z4,z5]),(0,[z0,z1,z2,z3,z215,z4,z5]),(1,[z0,z216,z2,z3,z4,z5])],[(0,[z0,z1,z217,z2,z3,z4,z5])],[(0,[z14,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z218,z5]),(0,[z0,z1,z219,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z220,z5])],[(1,[z0,z1,z2,z3,z4,z221]),(1,[z150,z1,z2,z3,z154,z5]),(0,[z0,z222,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z176,z5]),(0,[z0,z1,z223,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z224])],[(0,[z0,z1,z2,z3,z27,z51,z5]),(0,[z144,z0,z1,z2,z3,z4,z10])],[(0,[z0,z1,z2,z3,z13,z4,z5]),(1,[z225,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z226,z5])],[(0,[z227,z0,z1,z2,z3,z4,z5]),(1,[z228,z1,z2,z3,z4,z5])]],
   [[(0,[z229,z0,z1,z2,z3,z4,z5]),(0,[z19,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z230,z5])],[(1,[z0,z1,z2,z4,z231,z5]),(0,[z19,z0,z1,z2,z156,z4,z5]),(0,[z9,z0,z1,z2,z127,z4,z5]),(0,[z0,z1,z2,z124,z3,z64,z5]),(0,[z232,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z190,z28])],[(0,[z233,z1,z2,z3,z4,z114,z5]),(0,[z234,z0,z1,z2,z3,z4,z5]),(0,[z0,z44,z1,z166,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z235,z10]),(0,[z0,z1,z2,z3,z4,z10,z162]),(0,[z0,z1,z2,z76,z4,z28,z5]),(0,[z0,z1,z2,z3,z4,z5,z163])],[(0,[z0,z1,z2,z3,z236,z4,z5]),(1,[z0,z1,z2,z3,z4,z237]),(0,[z0,z1,z2,z3,z238,z4,z5])],[(0,[z0,z1,z2,z3,z239,z4,z5]),(0,[z0,z1,z2,z127,z18,z4,z5]),(0,[z0,z1,z166,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z240]),(0,[z0,z1,z2,z3,z241,z4,z5]),(1,[z90,z0,z2,z3,z51,z5]),(0,[z0,z1,z2,z3,z4,z242,z5])],[(0,[z94,z0,z1,z2,z3,z243,z5]),(0,[z0,z1,z244,z2,z3,z4,z5]),(0,[z0,z1,z2,z93,z151,z4,z5]),(0,[z0,z1,z2,z245,z3,z4,z5]),(0,[z0,z1,z246,z2,z3,z4,z5]),(1,[z0,z2,z3,z4,z10,z8]),(0,[z0,z1,z247,z2,z3,z4,z5]),(0,[z248,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z249,z4,z5])],[(0,[z0,z1,z2,z2,z3,z4,z5]),(0,[z250,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z251,z4,z5])],[(0,[z252,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z253,z2,z3,z4,z10]),(0,[z185,z0,z1,z2,z3,z116,z5]),(0,[z9,z185,z0,z1,z2,z4,z5]),(0,[z0,z1,z101,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z39,z5]),(0,[z0,z254,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z146,z4,z7,z5]),(0,[z0,z1,z2,z255,z3,z4,z5])]],
   [[(0,[z256,z0,z1,z2,z3,z4,z5]),(0,[z257,z0,z1,z2,z3,z4,z5]),(0,[z126,z0,z2,z127,z3,z4,z5]),(0,[z258,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z93,z3,z4,z8]),(0,[z196,z0,z1,z2,z3,z4,z137]),(0,[z0,z1,z2,z259,z3,z4,z5]),(0,[z0,z260,z1,z2,z3,z4,z5]),(0,[z9,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z27,z4,z10]),(0,[z0,z228,z1,z2,z3,z4,z5])],[(0,[z0,z1,z1,z2,z3,z4,z5]),(0,[z252,z0,z1,z2,z3,z4,z10]),(0,[z261,z0,z1,z2,z3,z4,z5]),(0,[z9,z0,z1,z2,z151,z4,z5]),(0,[z262,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z263]),(0,[z0,z1,z2,z3,z4,z39,z10]),(0,[z0,z1,z23,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z264]),(0,[z0,z1,z2,z3,z4,z5,z265])],[(0,[z0,z1,z2,z15,z3,z4,z8]),(0,[z0,z1,z23,z2,z93,z4,z5]),(0,[z266,z0,z1,z2,z3,z4,z5]),(0,[z267,z0,z1,z2,z3,z4,z5])],[(0,[z268,z0,z1,z2,z3,z4,z5]),(0,[z269,z0,z1,z2,z3,z4,z5]),(0,[z270,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z124,z3,z76,z5]),(0,[z144,z0,z216,z2,z3,z4,z5])],[(0,[z14,z0,z1,z2,z3,z4,z221]),(0,[z0,z1,z2,z3,z271,z4,z5]),(0,[z0,z1,z2,z272,z3,z4,z5]),(0,[z273,z0,z1,z2,z3,z4,z5])],[(0,[z41,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z274,z5]),(0,[z0,z1,z2,z4,z231,z154,z5]),(0,[z0,z1,z2,z3,z4,z275,z5]),(0,[z276,z0,z1,z2,z3,z4,z5])],[(0,[z0,z277,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z278,z5]),(0,[z0,z1,z2,z279,z3,z4,z5]),(0,[z280,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z281,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z5,z282]),(0,[z0,z1,z15,z45,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z283]),(0,[z284,z0,z1,z2,z3,z4,z5])],[(0,[z285,z0,z1,z2,z3,z4,z5]),(0,[z150,z1,z2,z3,z4,z154,z5]),(0,[z0,z1,z2,z3,z4,z8,z137]),(0,[z0,z1,z2,z3,z55,z4,z5]),(0,[z286,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z287]),(0,[z185,z0,z1,z2,z3,z4,z10]),(0,[z0,z288,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z289,z5])],[(0,[z0,z1,z290,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z291,z5]),(0,[z0,z135,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z292,z3,z4,z10]),(0,[z0,z1,z2,z293,z3,z4,z5]),(0,[z0,z1,z294,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z160,z4,z162])],[(0,[z0,z295,z1,z2,z3,z4,z5]),(0,[z145,z0,z1,z2,z3,z154,z5]),(0,[z113,z1,z2,z3,z4,z5,z138]),(0,[z296,z0,z1,z2,z3,z4,z5]),(0,[z32,z0,z1,z2,z3,z4,z8]),(0,[z0,z297,z1,z2,z3,z4,z5])],[(0,[z298,z0,z1,z2,z3,z4,z5])],[(0,[z0,z50,z1,z2,z3,z4,z299]),(0,[z0,z135,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z5,z300]),(0,[z0,z301,z1,z2,z3,z4,z5]),(1,[z196,z0,z1,z3,z4,z58])],[]],
   [[(0,[z302,z0,z1,z2,z3,z4,z5]),(0,[z303,z0,z1,z2,z3,z4,z5]),(0,[z9,z0,z1,z2,z4,z28,z5])],[(0,[z0,z1,z2,z304,z3,z4,z5]),(0,[z0,z1,z2,z3,z305,z4,z5]),(1,[z211,z0,z2,z3,z4,z10]),(0,[z306,z0,z1,z2,z3,z4,z5])],[(0,[z252,z1,z253,z2,z3,z4,z5]),(0,[z0,z1,z2,z143,z4,z5,z77])],[(0,[z0,z1,z2,z3,z4,z5,z307]),(0,[z0,z1,z2,z308,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z309]),(0,[z0,z1,z2,z3,z4,z190,z5])],[(0,[z0,z1,z2,z3,z70,z4,z8]),(0,[z0,z1,z2,z3,z4,z310,z5]),(0,[z0,z1,z2,z3,z4,z311,z5]),(1,[z0,z1,z2,z3,z4,z312]),(0,[z313,z0,z1,z2,z3,z4,z5]),(0,[z0,z50,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z314,z3,z4,z5]),(0,[z0,z1,z2,z3,z76,z4,z8]),(0,[z0,z2,z3,z4,z10,z5,z8]),(0,[z315,z0,z1,z2,z3,z4,z5])],[(0,[z94,z0,z277,z2,z3,z4,z5])],[(0,[z316,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z124,z3,z51,z5]),(0,[z0,z1,z2,z3,z4,z5,z317]),(0,[z318,z0,z1,z2,z3,z4,z5]),(0,[z0,z319,z1,z2,z3,z4,z5])],[(0,[z185,z0,z1,z2,z3,z203,z5]),(1,[z0,z1,z2,z320,z4,z5]),(0,[z0,z1,z321,z2,z3,z4,z5]),(0,[z0,z1,z2,z322,z3,z4,z5]),(0,[z36,z0,z1,z2,z3,z4,z8]),(0,[z323,z0,z1,z2,z3,z4,z5]),(0,[z324,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z143,z4,z77])]],
   [[(0,[z1,z2,z18,z3,z70,z4,z5]),(0,[z0,z1,z2,z3,z4,z10,z77]),(0,[z0,z1,z2,z3,z4,z325,z5]),(0,[z9,z228,z1,z2,z3,z4,z5]),(0,[z326,z0,z1,z2,z3,z4,z5])],[(0,[z144,z113,z0,z1,z2,z3,z4]),(0,[z0,z327,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z328]),(0,[z0,z1,z329,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z330,z5]),(0,[z0,z331,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z91]),(0,[z211,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z321,z2,z3,z4,z10])],[(1,[z0,z1,z2,z332,z4,z5]),(0,[z333,z0,z1,z2,z3,z4,z5]),(0,[z17,z0,z1,z2,z70,z4,z5]),(0,[z0,z334,z1,z2,z3,z4,z154]),(0,[z0,z1,z2,z3,z4,z335,z5]),(0,[z0,z1,z2,z3,z64,z65,z5]),(0,[z0,z1,z57,z2,z3,z4,z10])],[(0,[z336,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z154,z28,z5]),(0,[z0,z1,z2,z3,z4,z5,z337]),(0,[z0,z338,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z299]),(0,[z0,z1,z339,z2,z3,z4,z5]),(0,[z0,z1,z2,z322,z3,z4,z8]),(0,[z340,z0,z1,z2,z3,z4,z5])],[(0,[z0,z44,z1,z2,z3,z4,z10]),(0,[z0,z2,z3,z4,z51,z5,z8]),(0,[z211,z0,z1,z2,z3,z4,z10]),(1,[z0,z1,z2,z3,z4,z341]),(0,[z0,z1,z2,z342,z3,z4,z5]),(0,[z0,z1,z2,z143,z146,z4,z5])],[(0,[z343,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z198,z3,z4,z5]),(1,[z0,z1,z23,z37,z4,z5])],[(0,[z0,z344,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z143,z3,z4,z77])]],
   [[(0,[z345,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z346,z3,z4,z5]),(0,[z90,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z10,z8]),(0,[z0,z1,z2,z3,z4,z122,z8]),(0,[z0,z1,z2,z146,z3,z4,z5])],[(0,[z0,z1,z2,z347,z3,z4,z5]),(0,[z0,z1,z2,z18,z3,z4,z10]),(0,[z0,z1,z2,z3,z348,z4,z5])],[(1,[z0,z1,z2,z3,z4,z5]),(0,[z349,z0,z1,z2,z3,z4,z5]),(0,[z126,z0,z1,z2,z3,z4,z350]),(0,[z0,z1,z2,z124,z3,z4,z10])],[(1,[z0,z334,z1,z2,z3,z4]),(0,[z1,z2,z3,z4,z114,z5,z138]),(0,[z0,z1,z2,z3,z20,z4,z5]),(0,[z0,z1,z2,z351,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z85,z5]),(1,[z0,z1,z2,z3,z4,z148]),(0,[z185,z0,z1,z2,z18,z4,z5]),(0,[z352,z0,z1,z2,z3,z4,z5]),(0,[z353,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z127,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z354,z5]),(0,[z0,z1,z2,z146,z3,z160,z4])],[(0,[z185,z17,z1,z2,z3,z4,z5]),(0,[z0,z1,z355,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z28,z10]),(0,[z0,z1,z2,z3,z4,z356,z5])],[(1,[z106,z277,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z357]),(0,[z0,z1,z2,z358,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z45,z3,z4,z10]),(0,[z0,z1,z2,z151,z37,z4,z5]),(0,[z126,z0,z1,z2,z3,z4,z8]),(0,[z359,z0,z1,z2,z3,z4,z5])],[(0,[z0,z277,z1,z2,z3,z4,z85]),(0,[z0,z1,z2,z3,z360,z4,z5]),(0,[z0,z1,z2,z3,z4,z361,z5]),(0,[z362,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z363,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z7,z58])],[(0,[z94,z0,z1,z364,z3,z4,z5]),(0,[z94,z0,z1,z2,z13,z4,z5]),(0,[z365,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z366]),(0,[z19,z0,z1,z2,z3,z4,z312]),(0,[z0,z1,z367,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z368,z5])],[(0,[z369,z0,z1,z2,z3,z4,z5]),(0,[z370,z0,z1,z2,z3,z4,z5]),(0,[z90,z0,z2,z3,z4,z51,z5]),(0,[z0,z1,z2,z371,z3,z4,z5])],[(0,[z0,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z98,z5]),(0,[z0,z1,z2,z3,z372,z4,z5]),(1,[z0,z1,z2,z3,z373,z5]),(0,[z90,z0,z1,z2,z3,z64,z5]),(0,[z374,z0,z1,z2,z3,z4,z5]),(0,[z0,z375,z1,z2,z3,z4,z5]),(0,[z0,z1,z57,z2,z3,z4,z137])],[(0,[z376,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z231,z5]),(0,[z0,z1,z2,z3,z4,z299,z5])],[(0,[z0,z1,z2,z3,z377,z4,z5]),(0,[z0,z1,z2,z378,z3,z4,z5]),(0,[z0,z1,z2,z3,z379,z4,z5]),(0,[z0,z1,z2,z3,z380,z4,z5]),(0,[z0,z50,z1,z2,z381,z4,z5]),(0,[z168,z0,z1,z2,z3,z4,z8]),(0,[z382,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z107,z2,z3,z4,z5]),(0,[z383,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z384,z4,z5])]],
   [[(0,[z385,z0,z1,z2,z3,z4,z5]),(0,[z386,z0,z1,z2,z3,z4,z5]),(0,[z17,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z387,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z388,z5]),(0,[z0,z1,z2,z3,z4,z389,z5]),(0,[z0,z1,z2,z390,z3,z4,z5]),(0,[z391,z0,z1,z2,z3,z4,z5])],[(0,[z392,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z393,z3,z4,z5]),(0,[z0,z1,z2,z394,z3,z4,z5]),(0,[z0,z1,z395,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z396,z5]),(0,[z0,z1,z2,z3,z4,z397,z5]),(0,[z0,z1,z2,z398,z3,z4,z5])],[(0,[z0,z1,z2,z399,z3,z4,z5])],[(0,[z106,z0,z277,z2,z3,z4,z5]),(0,[z14,z0,z1,z2,z3,z4,z5]),(0,[z0,z132,z1,z2,z151,z4,z5])],[(0,[z0,z1,z400,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z8,z61]),(0,[z196,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z401,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z402]),(0,[z403,z0,z1,z2,z3,z4,z5]),(0,[z14,z0,z1,z2,z3,z4,z148]),(0,[z211,z0,z135,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z8,z77]),(0,[z144,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z116,z4,z5]),(0,[z404,z0,z1,z2,z3,z4,z5]),(0,[z19,z0,z44,z2,z3,z4,z5]),(0,[z405,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z74]),(0,[z0,z132,z1,z2,z3,z4,z8])],[(0,[z406,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z407,z3,z4,z5]),(0,[z0,z1,z2,z3,z65,z51,z5]),(0,[z408,z0,z1,z2,z3,z4,z10])]],
   [[(0,[z145,z1,z2,z3,z70,z4,z5]),(0,[z409,z0,z1,z2,z3,z4,z5]),(0,[z19,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z7,z10])],[(0,[z113,z0,z1,z2,z3,z4,z8]),(0,[z113,z0,z1,z2,z3,z160,z4]),(0,[z0,z1,z2,z3,z373,z4,z5]),(0,[z0,z1,z2,z3,z4,z410,z5]),(0,[z0,z1,z2,z3,z4,z411,z5]),(0,[z412,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z413,z5]),(0,[z0,z1,z101,z2,z3,z4,z414])],[(0,[z0,z1,z2,z3,z4,z235,z5]),(0,[z0,z1,z2,z3,z64,z154,z5]),(0,[z0,z415,z1,z2,z3,z4,z5]),(0,[z211,z0,z50,z2,z3,z4,z5]),(0,[z0,z416,z1,z2,z3,z4,z5])],[(0,[z106,z277,z1,z2,z3,z4,z5]),(0,[z126,z0,z1,z2,z3,z4,z172]),(0,[z0,z1,z2,z3,z4,z417,z5]),(0,[z0,z1,z23,z2,z37,z4,z5]),(0,[z0,z1,z2,z3,z418,z4,z5])],[(0,[z0,z1,z2,z419,z3,z4,z5]),(0,[z0,z1,z2,z3,z420,z4,z5]),(0,[z0,z1,z2,z3,z4,z421,z5]),(1,[z0,z1,z2,z381,z4,z5]),(0,[z0,z1,z101,z3,z65,z4,z5])],[(0,[z0,z277,z1,z2,z3,z4,z287]),(0,[z0,z1,z2,z198,z3,z4,z5]),(0,[z422,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z8,z8]),(0,[z0,z1,z2,z3,z423,z4,z5]),(0,[z0,z1,z2,z424,z3,z4,z5])],[(0,[z0,z1,z2,z425,z3,z4,z5]),(0,[z0,z1,z2,z3,z426,z4,z5]),(0,[z1,z2,z3,z27,z4,z154,z5]),(0,[z427,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z253,z2,z3,z4,z5]),(0,[z0,z1,z428,z2,z3,z4,z5]),(0,[z233,z0,z1,z2,z3,z4,z138]),(0,[z429,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z430]),(0,[z0,z1,z2,z146,z3,z4,z7]),(0,[z0,z1,z431,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z432,z4,z5]),(0,[z0,z1,z2,z3,z4,z433,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z402,z5]),(0,[z0,z1,z15,z3,z4,z5,z137]),(0,[z0,z1,z2,z3,z4,z230,z8]),(0,[z0,z1,z2,z3,z4,z10,z24]),(0,[z0,z1,z2,z3,z4,z10,z224]),(0,[z0,z1,z23,z2,z3,z4,z341]),(0,[z0,z1,z2,z434,z3,z4,z5])],[(0,[z0,z1,z2,z3,z27,z4,z5]),(0,[z233,z0,z1,z2,z3,z4,z5]),(1,[z435,z1,z2,z3,z4,z5]),(0,[z0,z436,z1,z2,z3,z4,z5])],[(0,[z19,z0,z1,z2,z3,z373,z5]),(1,[z0,z132,z2,z151,z4,z5]),(1,[z0,z135,z2,z3,z4,z8])],[(0,[z0,z1,z2,z437,z3,z4,z5]),(0,[z0,z1,z2,z3,z64,z4,z10]),(0,[z0,z1,z2,z3,z4,z438,z5]),(0,[z0,z216,z1,z2,z3,z4,z5])],[(0,[z252,z14,z1,z2,z3,z4,z5]),(0,[z0,z1,z253,z2,z3,z4,z8]),(0,[z196,z0,z1,z253,z3,z4,z5]),(0,[z233,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z166,z2,z3,z4,z8])],[(0,[z252,z1,z107,z2,z3,z4,z5]),(0,[z0,z439,z1,z2,z3,z4,z5]),(0,[z440,z0,z1,z2,z3,z4,z5]),(0,[z441,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z442,z4,z5]),(0,[z0,z1,z2,z3,z4,z443,z5]),(0,[z0,z1,z2,z3,z4,z444,z5]),(0,[z0,z1,z2,z445,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z10,z163])],[(0,[z94,z106,z1,z2,z3,z4,z5]),(0,[z252,z0,z1,z2,z3,z4,z8]),(1,[z113,z1,z2,z3,z4,z138]),(0,[z0,z1,z2,z3,z4,z5,z138]),(0,[z446,z0,z1,z2,z3,z4,z5]),(1,[z0,z50,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z39,z8]),(0,[z0,z1,z2,z3,z4,z447,z10]),(0,[z0,z1,z2,z3,z4,z448,z5])]],
   [[(0,[z14,z0,z1,z253,z3,z4,z5]),(1,[z252,z1,z253,z3,z4,z5]),(0,[z9,z0,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z449,z3,z4,z5]),(0,[z0,z1,z2,z3,z450,z4,z5]),(0,[z0,z1,z2,z3,z4,z451,z5]),(1,[z185,z1,z2,z70,z4,z5]),(0,[z0,z1,z2,z18,z124,z4,z5]),(0,[z0,z1,z452,z2,z3,z4,z5]),(0,[z0,z1,z453,z2,z3,z4,z5]),(0,[z90,z0,z1,z2,z3,z51,z5]),(0,[z144,z0,z1,z2,z3,z4,z137])],[(0,[z94,z0,z1,z2,z3,z4,z10]),(0,[z185,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z454]),(0,[z0,z1,z1,z2,z3,z4,z8]),(0,[z0,z1,z23,z2,z3,z4,z8]),(0,[z455,z0,z1,z2,z3,z4,z5])],[(0,[z0,z435,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z292,z3,z4,z5]),(0,[z196,z0,z1,z3,z4,z58,z5]),(0,[z144,z0,z1,z2,z3,z5,z163])],[(0,[z0,z1,z2,z3,z4,z456,z5]),(0,[z0,z1,z457,z2,z3,z4,z5]),(0,[z0,z458,z1,z2,z3,z4,z5]),(0,[z0,z1,z93,z3,z37,z4,z5]),(0,[z144,z0,z1,z2,z3,z160,z5])],[(1,[z0,z1,z2,z3,z4,z62])],[(0,[z0,z1,z2,z3,z154,z51,z5]),(0,[z41,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z459,z2,z3,z4,z5])],[(0,[z0,z460,z1,z2,z3,z4,z5]),(0,[z150,z145,z1,z2,z3,z4,z5]),(0,[z461,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z37,z4,z10]),(0,[z0,z1,z101,z2,z3,z65,z5]),(0,[z0,z1,z2,z3,z4,z5,z462])]],
   [[(0,[z0,z1,z2,z3,z4,z463,z5]),(0,[z0,z1,z2,z3,z4,z464,z5])],[(0,[z465,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z466,z5]),(0,[z150,z0,z1,z2,z3,z154,z5]),(1,[z0,z1,z2,z371,z4,z5]),(0,[z0,z467,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z468,z3,z4,z5]),(0,[z0,z1,z2,z469,z3,z4,z5])],[],[(0,[z0,z1,z2,z3,z4,z470,z5]),(0,[z471,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z472,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z473,z4,z5]),(0,[z126,z0,z1,z2,z3,z241,z5]),(0,[z0,z135,z1,z2,z3,z4,z8])],[(0,[z94,z0,z1,z2,z3,z4,z307]),(0,[z0,z1,z2,z474,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z475,z5]),(0,[z0,z1,z2,z3,z4,z476,z5]),(0,[z0,z1,z2,z3,z4,z5,z477])],[(0,[z478,z0,z1,z2,z3,z4,z5]),(0,[z19,z0,z1,z2,z3,z4,z240]),(0,[z479,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z480,z5]),(0,[z0,z1,z2,z481,z3,z4,z5])],[(0,[z252,z0,z1,z253,z3,z4,z5]),(0,[z17,z1,z2,z3,z4,z154,z5]),(0,[z0,z1,z2,z3,z4,z482,z5]),(0,[z19,z435,z1,z2,z3,z4,z5]),(0,[z0,z44,z166,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z483,z5]),(0,[z0,z1,z2,z3,z160,z4,z58]),(0,[z144,z0,z1,z2,z3,z4,z162]),(0,[z0,z1,z2,z3,z160,z4,z163])]],
   [[(0,[z145,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z51,z10])],[(0,[z484,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z485,z5]),(0,[z486,z0,z1,z2,z3,z4,z5]),(0,[z0,z487,z1,z2,z3,z4,z5])],[(0,[z0,z1,z488,z2,z3,z4,z5]),(0,[z150,z0,z1,z2,z3,z4,z10]),(0,[z0,z489,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z490,z5]),(0,[z0,z1,z491,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z10,z300]),(0,[z0,z1,z2,z492,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z154,z10]),(0,[z0,z1,z2,z3,z4,z58,z138]),(0,[z0,z1,z2,z3,z151,z4,z10]),(0,[z0,z1,z2,z127,z37,z4,z5]),(0,[z0,z1,z57,z2,z3,z4,z5])],[(0,[z0,z2,z127,z3,z151,z4,z5]),(0,[z0,z50,z1,z2,z3,z4,z8]),(0,[z0,z1,z493,z2,z3,z4,z5]),(0,[z494,z0,z1,z2,z3,z4,z5]),(0,[z32,z0,z1,z2,z3,z65,z5])],[(0,[z495,z0,z1,z2,z3,z4,z5]),(0,[z0,z44,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z496]),(0,[z0,z1,z3,z65,z4,z39,z5]),(0,[z0,z1,z2,z3,z4,z58,z5]),(0,[z0,z1,z2,z3,z4,z5,z137])],[(0,[z0,z1,z2,z3,z4,z5,z221]),(0,[z17,z0,z1,z2,z76,z4,z5]),(0,[z0,z1,z2,z3,z4,z497,z5])],[(1,[z0,z431,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z498,z5]),(0,[z17,z1,z2,z18,z3,z4,z5]),(0,[z0,z1,z57,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z58,z10]),(0,[z0,z1,z2,z499,z3,z4,z5]),(0,[z32,z0,z1,z101,z3,z4,z5]),(1,[z500,z1,z2,z3,z4,z5]),(0,[z501,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z146,z3,z4,z77])],[(0,[z0,z1,z2,z18,z3,z4,z5]),(0,[z0,z1,z2,z502,z3,z4,z5]),(0,[z196,z0,z1,z57,z3,z4,z5])],[(0,[z503,z0,z1,z2,z3,z4,z5]),(0,[z211,z0,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z5,z504]),(0,[z0,z1,z2,z505,z3,z4,z5]),(0,[z0,z1,z2,z124,z3,z4,z5]),(0,[z0,z1,z2,z3,z506,z4,z5])],[(0,[z0,z1,z2,z3,z4,z8,z163]),(0,[z0,z1,z2,z507,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z137,z77])],[(0,[z0,z508,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z350]),(0,[z0,z50,z1,z2,z3,z4,z509]),(0,[z500,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z151,z70,z4,z5]),(0,[z0,z1,z2,z127,z3,z4,z5]),(0,[z0,z1,z2,z151,z76,z4,z5]),(0,[z510,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z511,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z237]),(0,[z0,z1,z2,z3,z160,z162,z5])],[(0,[z0,z512,z1,z2,z3,z4,z5]),(0,[z0,z1,z253,z45,z3,z4,z5]),(0,[z0,z1,z513,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z240]),(0,[z0,z1,z2,z514,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z515,z10]),(0,[z0,z1,z2,z3,z160,z4,z10]),(0,[z0,z1,z23,z2,z3,z4,z516]),(0,[z0,z1,z2,z3,z4,z28,z5])],[(0,[z1,z107,z2,z15,z3,z4,z5]),(1,[z126,z0,z2,z127,z4,z5]),(0,[z0,z1,z2,z3,z4,z517,z5]),(0,[z0,z1,z2,z3,z4,z5,z518])]],
   [[(0,[z106,z0,z1,z2,z3,z4,z10]),(0,[z0,z334,z1,z2,z3,z4,z5]),(0,[z0,z1,z519,z2,z3,z4,z5]),(0,[z0,z1,z2,z45,z3,z4,z5]),(0,[z520,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z146,z3,z4,z8]),(1,[z0,z1,z57,z3,z4,z137]),(0,[z144,z0,z1,z2,z146,z3,z4])],[(1,[z0,z1,z95,z3,z4,z5]),(0,[z521,z0,z1,z2,z3,z4,z5]),(0,[z233,z0,z1,z2,z3,z4,z114]),(1,[z19,z0,z45,z3,z4,z5]),(1,[z0,z1,z2,z124,z76,z5])],[(0,[z522,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z98,z5]),(0,[z0,z1,z2,z523,z3,z4,z5]),(0,[z0,z1,z2,z524,z3,z4,z5]),(0,[z0,z1,z2,z525,z3,z4,z5]),(0,[z0,z1,z526,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z527,z5]),(0,[z0,z1,z2,z127,z3,z4,z8]),(1,[z0,z1,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z528,z4,z5]),(0,[z0,z1,z2,z529,z3,z4,z5])],[(1,[z0,z1,z2,z3,z181,z4]),(0,[z0,z132,z1,z2,z3,z4,z496])],[(0,[z0,z1,z2,z3,z530,z4,z5])],[(0,[z0,z44,z1,z2,z3,z4,z208]),(0,[z0,z1,z2,z531,z3,z4,z5]),(0,[z0,z1,z2,z532,z3,z4,z5])],[(0,[z0,z1,z2,z533,z3,z4,z5]),(0,[z534,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z535]),(0,[z0,z1,z2,z3,z64,z27,z5]),(0,[z113,z0,z1,z457,z3,z4,z5])]],
   [[(0,[z0,z1,z536,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z537])],[(0,[z0,z1,z364,z2,z3,z4,z5]),(0,[z0,z1,z2,z18,z4,z28,z5]),(0,[z0,z1,z538,z2,z3,z4,z5]),(0,[z539,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z395,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z8,z282]),(0,[z540,z0,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z509]),(0,[z144,z0,z431,z2,z3,z4,z5])],[(0,[z541,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z542])],[(0,[z0,z1,z2,z543,z3,z4,z5]),(1,[z0,z1,z2,z194,z4,z5]),(0,[z0,z1,z2,z3,z4,z544,z5]),(0,[z0,z1,z2,z545,z3,z4,z5])],[(0,[z0,z1,z2,z546,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z547]),(0,[z0,z548,z1,z2,z3,z4,z5])],[(0,[z549,z0,z1,z2,z3,z4,z5]),(0,[z233,z144,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z550,z10]),(0,[z0,z1,z2,z551,z3,z4,z5])],[(0,[z0,z1,z107,z2,z3,z4,z8]),(0,[z408,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z101,z2,z3,z4,z10]),(0,[z0,z1,z2,z552,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z553,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z389,z8]),(0,[z0,z1,z2,z3,z4,z7,z5]),(0,[z0,z1,z554,z2,z3,z4,z5])],[(0,[z0,z1,z2,z555,z3,z4,z5]),(0,[z556,z0,z1,z2,z3,z4,z5])],[(0,[z22,z0,z1,z2,z3,z4,z5]),(0,[z106,z1,z2,z15,z3,z4,z5]),(0,[z557,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z558,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z559,z4,z5]),(0,[z0,z1,z2,z3,z560,z4,z5]),(1,[z0,z44,z166,z3,z4,z5]),(0,[z561,z0,z1,z2,z3,z4,z5])],[(0,[z14,z0,z1,z2,z3,z4,z8]),(0,[z0,z562,z1,z2,z3,z4,z5])],[(0,[z563,z0,z1,z2,z3,z4,z5]),(0,[z0,z564,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z565,z4,z5]),(0,[z225,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z566,z5]),(0,[z0,z1,z2,z3,z4,z5,z567])],[(0,[z0,z1,z2,z332,z3,z4,z5]),(0,[z0,z1,z2,z568,z3,z4,z5]),(0,[z185,z0,z1,z2,z70,z4,z5]),(0,[z185,z0,z1,z2,z76,z4,z5]),(0,[z0,z1,z2,z569,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z172]),(0,[z144,z0,z1,z2,z3,z4,z8])],[(0,[z225,z0,z1,z2,z4,z154,z5]),(0,[z0,z570,z1,z2,z3,z4,z5])],[(1,[z0,z1,z364,z3,z4,z5]),(0,[z0,z277,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z312,z5]),(0,[z47,z0,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z146,z4,z7])]],
   [[(1,[z145,z1,z2,z3,z27,z5]),(0,[z19,z0,z1,z2,z3,z4,z8])],[(0,[z0,z1,z571,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z572,z4,z5]),(0,[z0,z1,z2,z3,z573,z4,z5]),(0,[z9,z500,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z574,z3,z4,z5])],[(0,[z575,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z576]),(0,[z0,z1,z2,z3,z4,z60,z5]),(0,[z9,z0,z1,z2,z3,z28,z5])],[(0,[z94,z0,z1,z2,z332,z4,z5]),(0,[z0,z1,z2,z3,z76,z154,z5]),(0,[z0,z1,z2,z3,z4,z5,z577]),(0,[z0,z1,z2,z3,z64,z4,z5]),(0,[z0,z1,z2,z3,z4,z578,z5]),(0,[z0,z579,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z65,z4,z5])],[(0,[z0,z1,z2,z3,z580,z4,z5]),(0,[z0,z1,z2,z581,z3,z4,z5]),(0,[z145,z0,z1,z2,z3,z27,z5]),(1,[z0,z1,z2,z3,z582,z5]),(0,[z0,z1,z2,z3,z4,z5,z91]),(0,[z32,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z5,z583])],[(0,[z0,z1,z584,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z58,z114]),(0,[z126,z0,z1,z2,z3,z582,z5]),(0,[z0,z585,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z586,z5])],[(0,[z150,z0,z1,z2,z3,z27,z5]),(0,[z0,z50,z1,z2,z371,z4,z5]),(0,[z0,z1,z2,z587,z3,z4,z5]),(0,[z0,z1,z2,z3,z65,z4,z10]),(1,[z0,z1,z2,z3,z4,z516]),(0,[z0,z1,z2,z3,z4,z588,z5])],[(0,[z589,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z194,z3,z4,z5]),(0,[z0,z1,z590,z2,z3,z4,z5]),(0,[z0,z132,z2,z3,z151,z4,z5]),(0,[z0,z1,z2,z3,z4,z447,z5]),(0,[z0,z1,z2,z3,z4,z5,z341]),(0,[z0,z1,z2,z3,z4,z591,z5]),(0,[z0,z1,z592,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z95,z3,z4,z5]),(0,[z593,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z594,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z595]),(0,[z0,z1,z2,z3,z27,z4,z8]),(0,[z233,z0,z1,z2,z3,z4,z8]),(0,[z233,z0,z1,z2,z3,z160,z4]),(0,[z0,z1,z2,z3,z4,z582,z5]),(0,[z36,z0,z1,z93,z3,z4,z5])],[(0,[z94,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z596,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z597]),(0,[z0,z1,z2,z156,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5,z598]),(0,[z0,z1,z2,z3,z4,z599,z5]),(0,[z0,z600,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z70,z4,z10]),(0,[z0,z1,z2,z3,z4,z5,z5]),(0,[z0,z1,z2,z3,z4,z601,z5]),(0,[z0,z1,z2,z3,z76,z4,z10]),(0,[z0,z1,z2,z3,z4,z7,z137]),(0,[z602,z0,z1,z2,z3,z4,z5])],[(0,[z94,z1,z107,z2,z3,z4,z5])],[(0,[z603,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z320,z4,z5]),(0,[z0,z1,z604,z2,z3,z4,z5]),(0,[z605,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z606,z2,z3,z4,z5])],[(0,[z150,z0,z1,z2,z320,z4,z5]),(0,[z36,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z37,z4,z5]),(0,[z0,z1,z2,z3,z607,z4,z5])]],
   [[(0,[z608,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z609,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z8,z357]),(0,[z0,z1,z2,z610,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z516,z5]),(0,[z0,z1,z2,z3,z611,z4,z5]),(0,[z0,z1,z101,z2,z3,z4,z237]),(0,[z0,z1,z2,z3,z612,z4,z5])],[(0,[z0,z1,z2,z3,z4,z88,z5]),(0,[z0,z1,z2,z3,z4,z613,z5])],[(0,[z185,z0,z1,z2,z3,z4,z8]),(0,[z19,z0,z1,z166,z3,z4,z5]),(0,[z36,z0,z1,z23,z3,z4,z5]),(0,[z0,z1,z614,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z615,z4,z5])],[(0,[z0,z1,z2,z3,z4,z10,z138]),(0,[z0,z1,z2,z616,z3,z4,z5]),(0,[z617,z0,z1,z2,z3,z4,z5]),(0,[z618,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z23,z3,z37,z4,z5])],[(0,[z0,z1,z619,z2,z3,z4,z5]),(0,[z620,z0,z1,z2,z3,z4,z5]),(1,[z144,z0,z1,z2,z3,z163])],[(1,[z0,z1,z2,z3,z243,z5]),(0,[z0,z1,z2,z124,z70,z4,z5]),(0,[z0,z1,z2,z3,z4,z621,z5]),(1,[z0,z1,z2,z3,z241,z5]),(0,[z0,z1,z2,z622,z3,z4,z5]),(0,[z0,z50,z2,z3,z64,z4,z5]),(0,[z623,z0,z1,z2,z3,z4,z5])],[(1,[z0,z50,z2,z3,z64,z5]),(0,[z0,z1,z2,z3,z624,z4,z5]),(0,[z0,z1,z2,z3,z4,z625,z5]),(0,[z626,z0,z1,z2,z3,z4,z5])],[(0,[z9,z0,z1,z2,z3,z64,z5]),(0,[z0,z1,z2,z627,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z127,z70,z4,z5]),(0,[z145,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z127,z76,z4,z5]),(0,[z90,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z51,z5]),(0,[z0,z1,z2,z3,z4,z10,z10]),(0,[z0,z628,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z629,z3,z4,z5])],[(0,[z0,z1,z253,z166,z3,z4,z5]),(0,[z0,z1,z2,z3,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z630,z5]),(0,[z0,z631,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z509])],[(0,[z0,z1,z2,z3,z4,z632,z5]),(0,[z150,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z633,z4,z5]),(0,[z0,z1,z2,z3,z4,z154,z5]),(0,[z0,z1,z2,z3,z151,z4,z5]),(0,[z634,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z635,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z636,z5])],[(0,[z0,z1,z2,z3,z181,z4,z154]),(1,[z362,z1,z2,z3,z4,z5]),(0,[z0,z1,z637,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z638,z4,z5]),(0,[z0,z1,z2,z3,z4,z639,z5])],[(0,[z94,z0,z1,z2,z3,z4,z402]),(0,[z17,z145,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z640,z5]),(0,[z641,z0,z1,z2,z3,z4,z5]),(0,[z196,z0,z1,z2,z3,z4,z58])],[(0,[z0,z1,z2,z3,z642,z4,z5]),(0,[z0,z1,z253,z3,z4,z5,z137]),(0,[z643,z0,z1,z2,z3,z4,z5]),(0,[z19,z0,z2,z45,z3,z4,z5]),(0,[z90,z0,z1,z2,z3,z4,z176]),(0,[z0,z1,z2,z3,z64,z39,z5]),(1,[z0,z1,z2,z3,z160,z162])],[(0,[z644,z0,z1,z2,z3,z4,z5]),(0,[z645,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z143,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z5,z646])]],
   [[(0,[z0,z647,z1,z2,z3,z4,z5]),(1,[z0,z1,z2,z3,z4,z287]),(0,[z0,z1,z2,z3,z4,z154,z8]),(1,[z0,z1,z457,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z648,z5]),(0,[z126,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z649,z2,z3,z4,z5])],[(0,[z0,z650,z1,z2,z3,z4,z5]),(0,[z651,z0,z1,z2,z3,z4,z5])],[(0,[z0,z652,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z114,z5]),(0,[z19,z0,z1,z45,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z208,z5]),(0,[z0,z1,z2,z3,z4,z5,z653]),(0,[z9,z0,z1,z2,z3,z76,z5]),(0,[z654,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z162,z5]),(0,[z144,z0,z1,z2,z3,z4,z163])],[(0,[z0,z1,z493,z2,z3,z4,z8]),(1,[z0,z1,z2,z3,z4,z414]),(0,[z0,z1,z2,z3,z4,z655,z5])],[(1,[z94,z107,z2,z3,z4,z5]),(0,[z0,z44,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z58,z8]),(0,[z0,z1,z2,z3,z4,z414,z5])],[(0,[z0,z1,z2,z18,z151,z4,z5]),(0,[z0,z1,z2,z656,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z515,z5]),(1,[z36,z0,z1,z93,z4,z5]),(0,[z657,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z160,z4,z5])],[(0,[z0,z1,z2,z3,z4,z658,z5]),(0,[z659,z0,z1,z2,z3,z4,z5])]],
   [[(0,[z106,z0,z1,z2,z3,z4,z5]),(0,[z17,z0,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z210,z4,z5]),(0,[z0,z1,z2,z3,z4,z660,z5]),(0,[z0,z661,z1,z2,z3,z4,z5])],[(1,[z0,z1,z2,z3,z4,z307]),(0,[z196,z0,z1,z15,z3,z4,z5]),(0,[z0,z1,z2,z18,z3,z4,z8]),(0,[z0,z662,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z10,z137])],[(0,[z0,z1,z2,z3,z663,z4,z5]),(0,[z0,z1,z2,z3,z4,z496,z5]),(0,[z0,z1,z2,z124,z3,z4,z8]),(0,[z0,z1,z664,z2,z3,z4,z5])],[(0,[z233,z113,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z665,z4,z5]),(0,[z666,z0,z1,z2,z3,z4,z5]),(0,[z0,z50,z1,z2,z3,z64,z5])],[(0,[z113,z0,z1,z2,z3,z4,z138]),(1,[z0,z1,z2,z20,z4,z5])],[(0,[z277,z1,z107,z2,z3,z4,z5]),(0,[z1,z253,z2,z15,z3,z4,z5]),(0,[z145,z1,z2,z3,z27,z4,z5]),(0,[z0,z1,z2,z667,z3,z4,z5]),(0,[z0,z1,z2,z48,z3,z4,z28])],[(0,[z0,z1,z2,z3,z668,z4,z5]),(0,[z0,z132,z1,z2,z3,z4,z10]),(0,[z669,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z28,z8]),(0,[z0,z1,z2,z670,z3,z4,z5])],[(0,[z671,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z672,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z8,z138]),(0,[z0,z1,z2,z45,z3,z4,z8]),(0,[z211,z0,z2,z3,z4,z51,z5]),(0,[z209,z0,z1,z2,z3,z4,z10]),(0,[z673,z0,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z203,z5]),(0,[z113,z0,z1,z2,z3,z4,z10]),(0,[z0,z674,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z93,z127,z4,z5])],[(0,[z19,z362,z1,z2,z3,z4,z5]),(0,[z675,z0,z1,z2,z3,z4,z5]),(0,[z676,z0,z1,z2,z3,z4,z5])],[(0,[z677,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z381,z4,z5]),(0,[z0,z1,z2,z3,z4,z8,z454]),(0,[z0,z1,z2,z3,z678,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z679])],[(0,[z0,z680,z1,z2,z3,z4,z5]),(0,[z681,z0,z1,z2,z3,z4,z5]),(0,[z9,z0,z1,z2,z3,z51,z5]),(0,[z0,z1,z2,z3,z4,z5,z682])],[(0,[z0,z1,z683,z2,z3,z4,z5]),(0,[z90,z0,z50,z2,z3,z4,z5]),(0,[z0,z1,z684,z2,z3,z4,z5]),(1,[z0,z1,z2,z48,z3,z4])],[(0,[z0,z1,z2,z3,z4,z114,z137]),(0,[z0,z1,z2,z3,z4,z550,z5]),(1,[z32,z0,z1,z3,z39,z5])],[(0,[z94,z0,z107,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z5,z685]),(0,[z0,z1,z2,z3,z4,z5,z62]),(0,[z0,z1,z2,z686,z3,z4,z5]),(0,[z0,z1,z101,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z687,z2,z3,z4,z5]),(0,[z688,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z76,z27,z5]),(0,[z0,z1,z2,z689,z3,z4,z5]),(0,[z0,z1,z2,z690,z3,z4,z5]),(0,[z258,z0,z1,z2,z3,z4,z5]),(0,[z691,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z93,z3,z4,z5])],[(0,[z0,z1,z166,z15,z3,z4,z5]),(0,[z692,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z693,z3,z4,z5]),(0,[z0,z1,z2,z3,z694,z4,z5]),(0,[z0,z1,z2,z3,z4,z695,z5])],[(0,[z0,z1,z696,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z350,z5]),(0,[z0,z1,z2,z3,z4,z10,z411]),(0,[z0,z1,z57,z3,z4,z5,z137]),(0,[z0,z1,z2,z3,z160,z4,z137]),(0,[z0,z1,z2,z4,z7,z5,z77])],[(0,[z0,z697,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z15,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z698,z5]),(0,[z126,z0,z132,z2,z3,z4,z5]),(0,[z0,z1,z2,z93,z3,z4,z10]),(0,[z0,z1,z2,z143,z3,z4,z7]),(0,[z0,z1,z2,z3,z4,z5,z699])],[(0,[z252,z106,z1,z2,z3,z4,z5]),(0,[z252,z0,z1,z15,z3,z4,z5]),(0,[z0,z1,z166,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z700,z5])],[(0,[z0,z1,z2,z3,z701,z4,z5]),(0,[z0,z1,z2,z3,z4,z10,z114]),(0,[z0,z2,z3,z64,z4,z51,z5]),(1,[z0,z2,z3,z4,z51,z8])],[(0,[z0,z1,z2,z3,z243,z4,z5]),(0,[z0,z1,z2,z15,z3,z4,z10]),(0,[z250,z0,z1,z2,z3,z4,z10])],[(0,[z0,z277,z1,z2,z3,z4,z5]),(0,[z702,z0,z1,z2,z3,z4,z5]),(0,[z703,z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z704,z4,z5]),(0,[z0,z1,z2,z705,z3,z4,z5]),(0,[z0,z1,z2,z3,z706,z4,z5])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z707,z5]),(0,[z0,z1,z2,z181,z4,z231]),(0,[z19,z362,z45,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z708]),(0,[z0,z1,z2,z371,z4,z8])],[(0,[z0,z1,z2,z3,z709,z5]),(0,[z0,z1,z2,z3,z710,z4]),(0,[z0,z1,z2,z3,z4,z711]),(0,[z0,z1,z2,z3,z241,z8]),(0,[z0,z1,z2,z3,z4,z712]),(0,[z0,z1,z2,z3,z4,z713])],[(0,[z0,z1,z2,z3,z714,z5]),(0,[z19,z435,z45,z3,z4,z5]),(0,[z0,z50,z2,z3,z64,z8]),(0,[z0,z1,z23,z37,z4,z10])],[(0,[z0,z1,z2,z3,z4,z715]),(0,[z0,z1,z2,z716,z4,z5]),(0,[z0,z1,z2,z3,z4,z717]),(0,[z718,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z719]),(0,[z0,z2,z3,z4,z10,z655]),(0,[z36,z0,z1,z720,z4,z5]),(1,[z0,z1,z2,z3,z721])],[(0,[z722,z0,z1,z3,z4,z5]),(1,[z1,z2,z3,z723,z5]),(0,[z724,z1,z2,z3,z4,z5]),(0,[z0,z166,z725,z3,z4,z5]),(0,[z726,z1,z2,z3,z4,z5])],[(0,[z14,z1,z15,z3,z4,z5]),(0,[z539,z1,z15,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z727]),(0,[z728,z1,z2,z3,z4,z5]),(0,[z0,z467,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z160,z162])],[(0,[z0,z1,z2,z3,z4,z10]),(0,[z71,z0,z1,z2,z28,z5]),(0,[z0,z1,z2,z3,z4,z729])],[(0,[z0,z1,z2,z3,z4,z287])]],
   [[(0,[z14,z1,z15,z3,z4,z10]),(0,[z362,z1,z2,z3,z4,z8]),(0,[z730,z1,z2,z3,z4,z5]),(0,[z0,z44,z725,z3,z4,z5])],[(0,[z0,z1,z2,z332,z4,z307]),(0,[z731,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z732]),(0,[z258,z1,z2,z3,z4,z138])],[(0,[z0,z1,z2,z733,z4,z5]),(0,[z0,z1,z513,z3,z4,z137]),(0,[z0,z1,z2,z156,z4,z10]),(0,[z0,z1,z725,z3,z4,z5]),(0,[z734,z1,z2,z3,z4,z5]),(0,[z0,z50,z2,z3,z64,z509]),(0,[z0,z2,z3,z4,z29,z10]),(0,[z0,z1,z2,z4,z5,z735])],[(0,[z0,z1,z2,z3,z4,z414]),(0,[z0,z1,z2,z3,z4,z736])],[(0,[z106,z277,z2,z3,z4,z287]),(0,[z17,z1,z2,z76,z154,z5]),(0,[z0,z1,z457,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z176]),(0,[z0,z1,z2,z371,z64,z5]),(0,[z0,z1,z2,z3,z4,z737]),(0,[z0,z1,z2,z3,z4,z738])],[(1,[z1,z2,z320,z154,z5]),(0,[z0,z739,z2,z3,z4,z5]),(0,[z0,z1,z554,z3,z4,z58])],[(0,[z47,z0,z2,z3,z51,z8])],[(0,[z0,z1,z2,z3,z243,z402]),(0,[z252,z1,z68,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z740]),(0,[z0,z50,z2,z3,z170,z5]),(0,[z500,z1,z2,z3,z4,z8]),(0,[z0,z1,z2,z124,z741,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z307]),(0,[z94,z107,z95,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z742]),(0,[z0,z1,z2,z3,z88,z240]),(0,[z0,z1,z2,z3,z373,z10]),(0,[z126,z0,z2,z127,z4,z350]),(0,[z0,z1,z2,z3,z4,z743])],[(0,[z94,z107,z2,z3,z98,z5]),(0,[z0,z1,z2,z744,z4,z5]),(0,[z94,z107,z2,z3,z4,z8]),(0,[z17,z1,z2,z4,z444,z5]),(0,[z0,z1,z2,z156,z373,z5]),(0,[z0,z1,z2,z3,z745,z5]),(0,[z9,z0,z2,z3,z51,z8]),(0,[z0,z1,z2,z3,z4,z746])],[(0,[z0,z1,z2,z3,z4,z747]),(0,[z233,z0,z431,z2,z3,z4]),(0,[z435,z1,z2,z3,z88,z5]),(0,[z0,z2,z3,z64,z748,z5]),(0,[z36,z0,z1,z93,z4,z8]),(0,[z0,z1,z2,z3,z160,z230])],[(0,[z0,z1,z2,z3,z203,z5]),(0,[z0,z1,z2,z20,z4,z5]),(0,[z0,z2,z3,z4,z447,z8])],[(0,[z0,z1,z2,z3,z4,z749]),(0,[z0,z750,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z241,z172]),(0,[z228,z1,z2,z127,z4,z5]),(1,[z0,z2,z3,z748,z5]),(0,[z0,z1,z2,z3,z4,z751])],[(0,[z0,z1,z2,z752,z4,z5]),(0,[z0,z1,z2,z753,z4,z5]),(0,[z0,z1,z2,z754,z4,z5]),(0,[z35,z0,z1,z3,z39,z5]),(0,[z0,z260,z2,z3,z4,z8]),(0,[z755,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z756]),(0,[z0,z1,z2,z3,z4,z757]),(0,[z0,z1,z758,z3,z4,z5]),(0,[z0,z1,z2,z759,z4,z8])],[]],
   [[(0,[z0,z1,z95,z3,z98,z5]),(0,[z0,z1,z2,z3,z760,z5]),(0,[z0,z1,z15,z3,z4,z221]),(0,[z276,z1,z15,z3,z4,z5]),(0,[z113,z1,z2,z3,z4,z24]),(0,[z0,z216,z2,z3,z4,z10])],[(1,[z761,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z762]),(0,[z0,z1,z2,z3,z763,z5]),(0,[z0,z1,z2,z3,z4,z721])],[(0,[z0,z1,z2,z3,z4,z764]),(0,[z14,z1,z15,z3,z4,z221]),(0,[z225,z0,z1,z2,z4,z5]),(0,[z0,z765,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z766])],[(0,[z106,z439,z2,z3,z4,z5]),(0,[z150,z1,z2,z3,z154,z10]),(0,[z0,z1,z2,z3,z4,z767]),(0,[z0,z1,z2,z3,z4,z768]),(0,[z0,z769,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z770])],[(0,[z0,z1,z2,z4,z231,z5]),(0,[z0,z1,z2,z3,z4,z771])],[(0,[z0,z1,z2,z3,z160,z361]),(0,[z228,z1,z2,z3,z4,z10]),(0,[z144,z0,z431,z2,z3,z163])],[(0,[z94,z107,z2,z3,z4,z402]),(0,[z0,z1,z2,z3,z4,z772]),(0,[z0,z50,z2,z3,z51,z8]),(0,[z0,z1,z2,z773,z4,z5])]],
   [[(0,[z0,z1,z2,z3,z4,z774]),(0,[z0,z1,z2,z3,z775,z5]),(0,[z0,z1,z2,z381,z4,z10]),(0,[z0,z619,z2,z3,z4,z8])],[(0,[z284,z1,z2,z18,z4,z5]),(0,[z0,z1,z2,z776,z4,z5])],[(0,[z0,z1,z2,z777,z4,z5]),(0,[z0,z1,z2,z3,z4,z778]),(0,[z32,z0,z1,z3,z39,z8]),(0,[z0,z2,z3,z4,z625,z8]),(0,[z0,z1,z2,z3,z4,z779])],[(0,[z90,z0,z2,z3,z51,z10]),(0,[z0,z1,z672,z3,z65,z5])],[(0,[z503,z1,z15,z3,z4,z5]),(0,[z0,z1,z2,z156,z4,z240]),(0,[z0,z2,z3,z4,z51,z8]),(0,[z0,z2,z3,z4,z10,z780])],[(0,[z0,z1,z2,z3,z4,z781]),(0,[z0,z1,z782,z3,z4,z5]),(0,[z435,z1,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z783])],[(0,[z435,z1,z2,z156,z4,z5]),(0,[z0,z132,z2,z151,z4,z10]),(0,[z0,z1,z784,z3,z4,z8]),(0,[z0,z1,z2,z146,z4,z785])],[(0,[z0,z1,z786,z3,z4,z5]),(0,[z0,z1,z2,z3,z787,z5]),(0,[z0,z1,z2,z320,z27,z5]),(0,[z0,z1,z2,z3,z4,z788]),(0,[z0,z487,z2,z3,z4,z8]),(0,[z0,z1,z2,z177,z4,z77])]],
   [[(0,[z0,z1,z789,z2,z3,z4]),(0,[z0,z1,z2,z790,z4,z5])],[(0,[z252,z1,z791,z3,z4,z5]),(0,[z0,z1,z792,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z793]),(0,[z126,z0,z2,z127,z4,z172]),(0,[z0,z1,z2,z371,z51,z5]),(0,[z267,z0,z2,z3,z4,z10]),(0,[z0,z661,z2,z3,z4,z10])],[(0,[z0,z1,z2,z3,z4,z794]),(0,[z19,z0,z725,z3,z4,z5]),(0,[z0,z1,z795,z3,z4,z5]),(0,[z47,z0,z1,z2,z3,z163])],[(0,[z9,z0,z1,z2,z483,z5]),(0,[z228,z1,z2,z4,z28,z5])],[(0,[z0,z1,z2,z796,z4,z5]),(0,[z252,z1,z253,z3,z4,z10]),(0,[z797,z0,z1,z2,z3,z5]),(0,[z0,z798,z2,z3,z4,z5])],[(0,[z0,z1,z95,z13,z4,z5]),(0,[z0,z1,z2,z799,z4,z5]),(0,[z800,z0,z1,z2,z3,z5]),(0,[z0,z431,z2,z143,z3,z4])],[(0,[z0,z1,z364,z3,z4,z8]),(0,[z0,z1,z364,z3,z98,z5]),(0,[z0,z1,z2,z13,z4,z8]),(0,[z0,z1,z2,z13,z98,z5]),(0,[z801,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z802]),(0,[z0,z803,z2,z3,z4,z5])],[(0,[z17,z1,z2,z804,z4,z5]),(0,[z145,z1,z2,z3,z27,z8]),(0,[z144,z0,z1,z198,z3,z4])]],
   [[(0,[z0,z1,z805,z3,z4,z5]),(0,[z196,z0,z1,z3,z4,z278]),(0,[z71,z1,z2,z3,z154,z5]),(0,[z126,z0,z2,z127,z582,z5]),(0,[z408,z1,z2,z3,z4,z24]),(0,[z0,z1,z2,z3,z4,z806])],[(0,[z0,z1,z2,z3,z4,z807])],[(0,[z0,z1,z2,z3,z4,z808]),(0,[z435,z1,z2,z20,z4,z5]),(0,[z0,z1,z2,z124,z169,z5]),(0,[z0,z1,z2,z3,z4,z809]),(0,[z196,z0,z1,z3,z4,z58])],[(0,[z0,z1,z2,z3,z4,z810]),(0,[z0,z1,z2,z3,z4,z74]),(0,[z0,z1,z2,z3,z582,z8]),(0,[z0,z1,z2,z3,z4,z811]),(0,[z0,z1,z720,z37,z4,z5])],[(0,[z0,z1,z2,z3,z4,z812]),(0,[z0,z1,z813,z3,z4,z5]),(0,[z0,z1,z2,z814,z4,z5]),(0,[z0,z431,z2,z3,z4,z58]),(0,[z0,z815,z2,z3,z4,z5]),(0,[z0,z431,z2,z3,z4,z163])],[(0,[z0,z1,z2,z3,z816,z5]),(0,[z0,z1,z2,z3,z4,z817]),(0,[z0,z1,z2,z3,z4,z818])],[(0,[z0,z1,z2,z3,z4,z819]),(0,[z0,z2,z3,z4,z10,z482]),(0,[z820,z0,z1,z2,z3,z4]),(0,[z209,z0,z1,z2,z3,z224])],[(0,[z0,z1,z2,z3,z821,z5]),(0,[z0,z1,z2,z4,z822,z5]),(0,[z47,z0,z1,z2,z3,z454]),(0,[z654,z0,z2,z3,z4,z10])]],
   [[(0,[z0,z1,z2,z3,z4,z823]),(0,[z0,z1,z2,z3,z4,z312]),(0,[z0,z1,z2,z3,z4,z824]),(1,[z0,z1,z720,z4,z5])],[(0,[z0,z1,z2,z3,z4,z825])],[(0,[z0,z1,z826,z2,z3,z4]),(0,[z185,z1,z2,z70,z203,z5]),(0,[z19,z0,z45,z3,z88,z5]),(0,[z0,z1,z93,z720,z4,z5]),(0,[z9,z0,z1,z2,z28,z5])],[(0,[z1,z2,z70,z4,z203,z5]),(0,[z0,z1,z2,z320,z4,z5]),(0,[z0,z1,z827,z3,z4,z5]),(0,[z0,z1,z2,z3,z88,z8]),(0,[z9,z228,z1,z2,z28,z5])],[(0,[z0,z1,z2,z13,z4,z402]),(0,[z0,z1,z3,z4,z736,z5])],[(0,[z0,z828,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z829]),(0,[z0,z415,z2,z3,z4,z8]),(0,[z0,z1,z720,z3,z4,z5]),(0,[z0,z1,z57,z3,z4,z736])],[(0,[z0,z1,z2,z3,z830,z5]),(0,[z0,z1,z2,z3,z116,z5]),(0,[z0,z1,z2,z3,z241,z350]),(0,[z0,z1,z2,z3,z4,z91]),(0,[z0,z1,z2,z831,z4,z5])],[(0,[z0,z1,z2,z332,z4,z5]),(0,[z0,z1,z832,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z833]),(0,[z0,z1,z664,z3,z4,z58])]],
   [[(0,[z0,z1,z3,z4,z834,z5]),(0,[z0,z1,z198,z3,z4,z138]),(0,[z0,z1,z2,z3,z4,z835])],[(0,[z0,z1,z2,z3,z836,z5]),(0,[z0,z1,z2,z3,z837,z5]),(0,[z838,z1,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z839,z5]),(0,[z0,z1,z2,z840,z4,z5]),(0,[z0,z1,z2,z146,z4,z122])],[(0,[z0,z1,z2,z3,z373,z312]),(0,[z0,z2,z840,z3,z4,z5]),(0,[z0,z1,z23,z37,z4,z5])],[(0,[z0,z1,z95,z3,z243,z5]),(0,[z0,z1,z841,z3,z4,z5]),(0,[z0,z1,z2,z3,z842,z5]),(0,[z0,z1,z2,z3,z843,z5]),(0,[z0,z1,z23,z720,z4,z5])],[(0,[z0,z1,z2,z3,z243,z8]),(0,[z17,z1,z2,z18,z4,z8]),(0,[z0,z2,z840,z151,z4,z5]),(0,[z0,z1,z2,z844,z4,z5]),(0,[z0,z1,z2,z292,z4,z7])],[(0,[z0,z845,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z846,z5]),(0,[z0,z1,z2,z847,z4,z5]),(0,[z0,z1,z198,z3,z4,z10]),(0,[z0,z1,z2,z848,z4,z5])],[(0,[z0,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z849,z5]),(0,[z0,z1,z2,z70,z203,z5]),(0,[z0,z1,z2,z76,z203,z5]),(0,[z185,z228,z1,z2,z4,z5]),(0,[z850,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z851,z5]),(0,[z0,z1,z2,z3,z582,z172]),(0,[z196,z0,z1,z3,z4,z736]),(0,[z228,z1,z2,z124,z4,z5])],[(0,[z185,z1,z2,z804,z4,z5]),(0,[z150,z1,z2,z3,z723,z5]),(0,[z0,z334,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z852]),(0,[z0,z1,z2,z3,z160,z695])]],
   [[(0,[z0,z1,z853,z3,z4,z5]),(0,[z854,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z855]),(0,[z0,z1,z2,z3,z4,z856])],[(0,[z0,z415,z2,z3,z64,z5]),(0,[z0,z2,z725,z3,z4,z5])],[(0,[z106,z1,z95,z3,z4,z5]),(0,[z14,z1,z15,z3,z4,z148]),(0,[z0,z1,z2,z857,z3,z4]),(0,[z0,z1,z2,z156,z4,z5]),(0,[z0,z1,z3,z4,z858,z10]),(0,[z0,z1,z67,z3,z4,z137])],[(0,[z0,z1,z2,z4,z859,z5]),(0,[z0,z1,z2,z3,z4,z860])],[],[(0,[z0,z1,z2,z3,z4,z861]),(0,[z14,z1,z15,z3,z4,z8]),(0,[z113,z0,z431,z2,z3,z4]),(1,[z0,z1,z2,z741,z5])],[(0,[z106,z277,z2,z3,z4,z10]),(0,[z1,z400,z15,z3,z4,z5]),(0,[z0,z1,z2,z3,z862,z5]),(0,[z0,z1,z2,z3,z4,z780])],[(0,[z0,z1,z2,z863,z4,z5]),(0,[z864,z0,z1,z2,z3,z4]),(0,[z0,z1,z2,z156,z4,z8]),(0,[z0,z1,z2,z3,z4,z865]),(0,[z0,z1,z2,z3,z4,z866])]],
   [[(0,[z0,z1,z867,z3,z4,z5]),(0,[z150,z1,z2,z320,z154,z5]),(0,[z113,z1,z2,z3,z4,z793]),(0,[z0,z1,z2,z3,z373,z5]),(0,[z0,z1,z2,z3,z4,z868]),(0,[z0,z1,z3,z4,z736,z137])],[(0,[z150,z225,z1,z2,z154,z5])],[(0,[z0,z216,z2,z3,z4,z299]),(0,[z0,z1,z2,z3,z4,z190])],[(0,[z0,z1,z2,z804,z4,z5]),(0,[z0,z1,z2,z3,z4,z869]),(0,[z0,z132,z2,z151,z4,z74]),(0,[z0,z1,z493,z3,z4,z137])],[(0,[z94,z761,z2,z3,z4,z5]),(0,[z1,z2,z3,z4,z870,z5]),(0,[z0,z1,z2,z3,z55,z447]),(0,[z9,z500,z1,z2,z28,z5])],[(0,[z225,z0,z334,z1,z2,z4]),(0,[z0,z1,z871,z3,z4,z5])],[(0,[z0,z1,z2,z3,z872,z4])],[(0,[z0,z1,z95,z3,z4,z307]),(0,[z0,z1,z2,z873,z4,z5]),(0,[z435,z1,z2,z3,z4,z312]),(0,[z0,z1,z2,z3,z4,z208]),(0,[z0,z1,z874,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z875])]],
   [[(0,[z0,z1,z2,z3,z98,z307]),(0,[z0,z216,z2,z3,z4,z5]),(0,[z0,z50,z2,z3,z4,z876])],[(0,[z0,z1,z364,z3,z243,z5]),(0,[z276,z1,z2,z3,z4,z138])],[(0,[z0,z1,z2,z877,z4,z5]),(0,[z0,z2,z3,z4,z83,z8]),(0,[z19,z0,z45,z20,z4,z5]),(0,[z0,z1,z878,z3,z4,z5]),(0,[z0,z1,z2,z3,z55,z162])],[(0,[z0,z1,z2,z3,z4,z221]),(0,[z0,z1,z791,z3,z4,z5]),(0,[z0,z1,z2,z3,z203,z8]),(0,[z0,z1,z879,z3,z4,z5]),(0,[z150,z1,z2,z3,z154,z5]),(0,[z0,z1,z2,z3,z4,z880]),(0,[z145,z1,z2,z3,z723,z5]),(0,[z0,z1,z2,z20,z4,z8]),(0,[z0,z1,z3,z4,z881,z5]),(0,[z90,z0,z2,z3,z51,z91]),(0,[z129,z0,z2,z3,z51,z5])],[(0,[z0,z1,z882,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z883]),(0,[z0,z1,z2,z3,z4,z884])],[(0,[z14,z1,z791,z3,z4,z5]),(0,[z0,z1,z2,z885,z4,z5]),(0,[z886,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z887]),(0,[z196,z0,z1,z3,z4,z389])],[(0,[z228,z1,z2,z3,z4,z5]),(0,[z225,z228,z1,z2,z4,z5]),(0,[z0,z44,z166,z3,z4,z10]),(0,[z0,z50,z2,z3,z4,z91])],[(0,[z1,z2,z3,z320,z154,z5]),(0,[z0,z132,z2,z840,z4,z5]),(0,[z0,z1,z2,z3,z4,z888]),(0,[z0,z2,z3,z4,z104,z8])]],
   [[(0,[z0,z1,z2,z3,z4,z889]),(0,[z1,z2,z320,z4,z154,z5]),(0,[z0,z890,z1,z2,z3,z4]),(0,[z119,z0,z2,z3,z4,z10]),(0,[z228,z1,z2,z151,z4,z5]),(0,[z0,z1,z2,z381,z4,z5]),(0,[z0,z1,z2,z3,z4,z891]),(0,[z144,z0,z1,z2,z3,z721])],[(0,[z0,z1,z2,z3,z4,z892]),(1,[z1,z2,z70,z203,z5]),(0,[z1,z2,z804,z70,z4,z5]),(0,[z0,z1,z2,z893,z4,z5]),(0,[z0,z1,z894,z2,z3,z4])],[(0,[z225,z0,z1,z2,z4,z8]),(0,[z0,z1,z2,z3,z4,z237])],[(0,[z0,z1,z2,z3,z4,z895]),(0,[z0,z1,z2,z3,z4,z240]),(0,[z0,z1,z2,z896,z4,z5]),(0,[z0,z1,z2,z3,z4,z897]),(0,[z90,z0,z2,z3,z51,z5]),(0,[z0,z1,z2,z898,z4,z5]),(0,[z0,z570,z2,z3,z4,z8])],[(0,[z0,z1,z2,z899,z4,z5]),(0,[z0,z260,z2,z3,z64,z5]),(0,[z0,z2,z3,z4,z10,z8])],[(0,[z435,z1,z2,z3,z4,z5]),(0,[z185,z1,z2,z70,z116,z5]),(0,[z0,z1,z2,z4,z231,z8]),(0,[z0,z2,z502,z3,z4,z10])],[(0,[z501,z1,z2,z3,z27,z5]),(0,[z0,z1,z2,z3,z900,z5]),(0,[z0,z132,z2,z151,z4,z5]),(0,[z0,z2,z3,z748,z51,z5]),(0,[z0,z1,z2,z3,z4,z901])],[(0,[z0,z1,z2,z3,z4,z902])]],
   [[(0,[z0,z1,z2,z3,z4,z903]),(0,[z0,z1,z2,z904,z4,z5]),(0,[z90,z0,z2,z3,z51,z8]),(0,[z0,z1,z2,z3,z4,z905])],[(0,[z94,z107,z364,z3,z4,z5]),(0,[z94,z107,z2,z13,z4,z5]),(0,[z0,z135,z2,z3,z4,z780]),(0,[z168,z0,z1,z3,z4,z389])],[(0,[z0,z1,z2,z906,z4,z5]),(0,[z0,z1,z2,z3,z4,z907]),(0,[z0,z1,z2,z3,z4,z908]),(0,[z0,z1,z2,z3,z909,z5]),(0,[z150,z334,z1,z2,z3,z154]),(0,[z0,z1,z198,z3,z4,z114]),(0,[z0,z1,z2,z3,z4,z910]),(0,[z0,z1,z3,z4,z58,z736]),(0,[z0,z1,z2,z3,z741,z5]),(0,[z0,z911,z2,z3,z4,z5])],[(0,[z692,z0,z2,z3,z4,z8]),(0,[z113,z1,z2,z3,z4,z138]),(0,[z0,z50,z2,z3,z4,z8]),(0,[z0,z40,z2,z3,z4,z8])],[(0,[z252,z1,z253,z3,z4,z5])],[(0,[z0,z1,z364,z3,z4,z307]),(0,[z144,z0,z1,z2,z3,z480]),(0,[z362,z1,z2,z3,z88,z5]),(0,[z912,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z373,z240]),(0,[z0,z1,z913,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z914]),(0,[z1,z253,z791,z3,z4,z5]),(0,[z0,z153,z166,z3,z4,z5]),(1,[z1,z2,z804,z4,z5]),(0,[z0,z1,z2,z3,z4,z915]),(0,[z0,z50,z2,z3,z748,z5])],[(0,[z0,z1,z2,z3,z916,z4]),(0,[z864,z0,z1,z2,z3,z203]),(0,[z435,z1,z2,z3,z373,z5]),(0,[z0,z2,z3,z51,z230,z8]),(0,[z0,z2,z3,z4,z8,z25]),(0,[z917,z1,z2,z3,z4,z5])]],
   [[(0,[z0,z1,z253,z3,z4,z221]),(0,[z185,z1,z2,z70,z4,z10]),(0,[z0,z1,z2,z3,z582,z350]),(0,[z0,z2,z161,z3,z4,z8])],[(0,[z17,z228,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z918])],[(0,[z32,z0,z1,z3,z919,z5]),(0,[z0,z1,z2,z143,z432,z4])],[(0,[z113,z436,z1,z2,z3,z4]),(0,[z0,z1,z2,z3,z920,z5]),(0,[z0,z2,z3,z4,z748,z5]),(0,[z0,z173,z2,z3,z4,z8]),(0,[z921,z0,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z160,z721])],[(0,[z0,z1,z2,z3,z4,z922]),(0,[z797,z0,z1,z2,z3,z8])],[(0,[z0,z1,z2,z923,z4,z5]),(0,[z0,z1,z2,z3,z924,z5]),(0,[z0,z1,z2,z3,z4,z925]),(0,[z0,z1,z2,z3,z4,z926])],[(1,[z1,z791,z3,z4,z5]),(0,[z269,z0,z1,z3,z4,z58]),(0,[z0,z2,z3,z51,z39,z8]),(0,[z0,z1,z2,z3,z927,z4]),(0,[z0,z1,z2,z3,z4,z928])],[(0,[z0,z1,z2,z3,z4,z929])]],
   [[(0,[z409,z0,z1,z2,z28,z5]),(0,[z0,z1,z2,z371,z4,z10]),(0,[z0,z458,z2,z3,z4,z8]),(0,[z211,z0,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z930,z5])],[(0,[z0,z1,z2,z3,z4,z931]),(0,[z0,z1,z2,z3,z932,z5]),(0,[z0,z334,z1,z2,z4,z231]),(0,[z0,z1,z2,z3,z241,z10])],[(0,[z0,z50,z2,z3,z64,z10])],[(0,[z0,z933,z2,z3,z4,z5]),(0,[z0,z1,z2,z934,z3,z4]),(0,[z0,z662,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z876]),(0,[z0,z1,z2,z3,z4,z935])],[(0,[z318,z1,z2,z70,z4,z5])],[(0,[z0,z1,z2,z20,z88,z5]),(0,[z144,z0,z1,z2,z3,z567])],[(0,[z0,z1,z2,z545,z76,z5]),(0,[z0,z217,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z936]),(0,[z0,z1,z493,z3,z4,z61]),(0,[z0,z1,z2,z143,z4,z77])],[(0,[z94,z107,z2,z3,z243,z5]),(0,[z385,z1,z15,z3,z4,z5]),(0,[z0,z219,z2,z3,z4,z8]),(0,[z19,z0,z45,z3,z4,z312]),(0,[z0,z1,z2,z4,z822,z8]),(0,[z9,z0,z1,z2,z202,z5])]],
   [[(0,[z0,z1,z2,z937,z4,z5]),(0,[z362,z1,z2,z3,z4,z10]),(0,[z0,z1,z23,z37,z4,z341]),(0,[z0,z1,z2,z720,z4,z5]),(0,[z0,z938,z2,z3,z4,z5]),(1,[z0,z1,z3,z4,z736])],[(0,[z0,z2,z3,z27,z51,z8]),(0,[z362,z1,z2,z156,z4,z5]),(0,[z0,z1,z2,z939,z4,z5]),(0,[z0,z1,z2,z940,z3,z4]),(0,[z0,z1,z2,z3,z4,z941])],[(0,[z435,z1,z2,z3,z4,z240]),(0,[z9,z0,z1,z2,z28,z8]),(0,[z0,z1,z2,z177,z4,z357])],[(0,[z0,z1,z2,z3,z243,z307]),(0,[z0,z1,z2,z3,z4,z942]),(0,[z0,z1,z2,z3,z943,z5]),(0,[z0,z1,z2,z320,z4,z8]),(0,[z0,z1,z2,z3,z4,z944]),(0,[z0,z1,z2,z3,z4,z299]),(0,[z0,z431,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z945]),(0,[z0,z1,z2,z3,z4,z341])],[(0,[z0,z1,z198,z3,z4,z5]),(0,[z9,z0,z1,z2,z203,z5]),(0,[z225,z1,z2,z70,z4,z5]),(0,[z0,z50,z2,z381,z4,z8]),(0,[z0,z2,z3,z4,z780,z5]),(0,[z0,z2,z574,z3,z4,z10])],[(0,[z0,z1,z95,z332,z4,z5]),(0,[z0,z1,z364,z13,z4,z5]),(0,[z0,z1,z2,z3,z116,z8]),(0,[z0,z428,z2,z3,z4,z10]),(0,[z0,z431,z2,z3,z4,z10])],[(0,[z0,z1,z2,z332,z4,z8]),(0,[z0,z1,z2,z332,z98,z5]),(0,[z258,z1,z2,z3,z4,z282]),(0,[z500,z1,z2,z3,z4,z10])]],
   [[(0,[z0,z1,z2,z3,z4,z946]),(0,[z1,z2,z18,z804,z4,z5]),(0,[z0,z1,z2,z3,z4,z947]),(1,[z0,z1,z2,z4,z785])],[(0,[z94,z107,z2,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z948]),(0,[z1,z2,z3,z4,z839,z8])],[(0,[z0,z1,z198,z3,z160,z4]),(0,[z0,z1,z3,z4,z858,z5]),(0,[z0,z1,z23,z37,z4,z8]),(0,[z36,z0,z1,z93,z4,z10]),(0,[z949,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z950,z4,z5]),(0,[z0,z1,z2,z3,z4,z148]),(0,[z324,z0,z2,z3,z51,z5]),(0,[z0,z1,z2,z3,z843,z8])],[(0,[z0,z951,z2,z3,z4,z5]),(0,[z0,z1,z57,z3,z4,z137])],[(0,[z692,z0,z45,z3,z4,z5]),(0,[z0,z1,z2,z3,z952,z5]),(0,[z362,z1,z2,z20,z4,z5]),(1,[z0,z725,z3,z4,z5]),(0,[z0,z301,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z98,z5]),(0,[z0,z1,z2,z3,z4,z8]),(0,[z106,z277,z2,z3,z4,z5]),(0,[z225,z17,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z953]),(0,[z126,z0,z2,z127,z4,z10])],[(0,[z0,z1,z2,z3,z954,z5]),(0,[z0,z1,z2,z4,z955,z5]),(0,[z0,z2,z3,z4,z8,z646])]],
   [[(0,[z0,z1,z95,z3,z4,z10]),(0,[z0,z1,z956,z3,z4,z5]),(0,[z19,z0,z45,z3,z4,z10]),(0,[z0,z1,z2,z124,z76,z10])],[(0,[z0,z1,z2,z3,z98,z10]),(0,[z277,z761,z2,z3,z4,z5]),(0,[z957,z0,z1,z2,z3,z4]),(0,[z19,z0,z45,z156,z4,z5]),(0,[z0,z1,z2,z3,z748,z5])],[],[(0,[z94,z107,z2,z3,z4,z307]),(0,[z0,z1,z2,z3,z958,z5]),(0,[z0,z1,z2,z3,z5,z959])],[(0,[z0,z1,z2,z3,z960,z5]),(0,[z0,z1,z2,z3,z4,z961]),(0,[z0,z962,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z963])],[(0,[z0,z1,z2,z332,z4,z402]),(0,[z0,z1,z2,z3,z4,z964]),(0,[z0,z1,z2,z965,z3,z4]),(0,[z966,z1,z2,z3,z4,z5])],[(0,[z0,z1,z967,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z509])],[(0,[z0,z1,z874,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z968]),(0,[z19,z0,z45,z3,z373,z5]),(0,[z0,z1,z2,z3,z4,z969]),(0,[z0,z431,z2,z3,z4,z137])]],
   [[(0,[z0,z1,z2,z970,z3,z4]),(0,[z0,z1,z2,z194,z4,z5]),(0,[z0,z1,z2,z3,z373,z8]),(0,[z0,z1,z2,z322,z4,z122]),(0,[z0,z1,z2,z4,z5,z785])],[(0,[z0,z1,z2,z3,z4,z971]),(0,[z0,z1,z2,z972,z4,z5]),(0,[z973,z1,z2,z3,z4,z5]),(0,[z9,z0,z1,z2,z741,z5])],[(0,[z974,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z975]),(0,[z32,z0,z1,z3,z39,z10]),(0,[z976,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z194,z4,z10]),(0,[z1,z2,z3,z4,z793,z138]),(0,[z0,z1,z2,z3,z977,z5]),(0,[z0,z1,z2,z978,z4,z5]),(0,[z0,z416,z2,z3,z4,z8]),(0,[z0,z1,z2,z979,z3,z4])],[(0,[z0,z1,z2,z3,z4,z402]),(0,[z0,z1,z2,z980,z4,z5]),(0,[z0,z1,z2,z13,z243,z5]),(0,[z225,z0,z1,z2,z28,z5]),(0,[z0,z1,z2,z3,z4,z981]),(0,[z9,z0,z1,z2,z291,z5]),(0,[z0,z319,z2,z3,z4,z8])],[(0,[z0,z2,z304,z3,z4,z8]),(0,[z1,z2,z3,z4,z793,z5]),(0,[z0,z1,z2,z381,z4,z299]),(0,[z0,z1,z57,z3,z4,z411]),(0,[z0,z982,z2,z3,z4,z5]),(0,[z0,z1,z2,z76,z741,z5]),(0,[z0,z1,z2,z143,z4,z785])],[(0,[z0,z1,z2,z3,z983,z5]),(0,[z0,z984,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z985]),(0,[z0,z44,z166,z3,z4,z5])],[(0,[z0,z1,z2,z3,z986,z5]),(0,[z0,z725,z45,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z987]),(0,[z0,z1,z2,z988,z4,z5])]],
   [[(0,[z0,z1,z989,z2,z3,z4]),(0,[z0,z1,z2,z990,z4,z5]),(0,[z0,z1,z2,z3,z4,z991]),(0,[z0,z1,z2,z3,z4,z992]),(0,[z0,z216,z2,z3,z4,z8]),(0,[z993,z1,z2,z3,z4,z5])],[(0,[z1,z2,z3,z4,z723,z5])],[(0,[z0,z1,z994,z3,z4,z5]),(0,[z0,z2,z124,z3,z51,z8]),(0,[z0,z1,z878,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z995]),(0,[z150,z1,z2,z3,z154,z8]),(0,[z556,z0,z2,z127,z4,z5])],[(0,[z0,z1,z2,z3,z4,z996]),(0,[z0,z1,z2,z3,z4,z997]),(0,[z0,z2,z127,z840,z4,z5]),(0,[z0,z1,z2,z998,z4,z5])],[(0,[z0,z1,z2,z3,z4,z999]),(0,[z0,z1000,z2,z3,z4,z5]),(0,[z0,z1,z2,z1001,z4,z5]),(0,[z1002,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z785])],[(0,[z0,z1,z364,z3,z4,z10]),(0,[z0,z1,z2,z13,z4,z10]),(0,[z0,z1,z2,z76,z81,z5]),(0,[z0,z331,z2,z3,z4,z10]),(0,[z228,z1,z2,z3,z4,z8]),(0,[z0,z1,z23,z37,z4,z516])],[(0,[z0,z1,z2,z3,z4,z1003]),(0,[z225,z0,z1,z2,z181,z4]),(0,[z145,z1,z2,z3,z27,z10])]],
   [[(0,[z0,z1,z2,z3,z4,z1004]),(0,[z1005,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z1006,z5]),(0,[z0,z1,z2,z381,z4,z8]),(0,[z0,z1,z2,z259,z4,z7]),(0,[z144,z0,z216,z2,z3,z163])],[(0,[z0,z1,z2,z3,z1007,z5]),(0,[z0,z135,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z1008]),(0,[z0,z1009,z2,z3,z4,z5])],[(0,[z17,z1,z2,z387,z4,z5]),(0,[z113,z1,z198,z3,z4,z138]),(0,[z19,z0,z45,z3,z4,z240]),(0,[z0,z254,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z4,z516])],[(0,[z1010,z0,z1,z2,z3,z5]),(0,[z0,z1,z2,z3,z582,z10])],[(0,[z0,z1,z2,z3,z4,z1011])],[(0,[z150,z1,z2,z194,z154,z5]),(0,[z435,z1,z2,z3,z4,z8]),(0,[z9,z0,z1,z2,z128,z5]),(0,[z0,z1,z2,z1012,z3,z4]),(0,[z0,z1,z2,z741,z28,z5])],[(0,[z0,z1,z2,z3,z1013,z5]),(0,[z0,z1,z2,z3,z4,z1014]),(0,[z0,z1,z2,z3,z4,z1015]),(0,[z0,z132,z2,z151,z4,z8]),(0,[z0,z1,z294,z3,z4,z137])],[(0,[z0,z1,z2,z3,z4,z1016]),(0,[z0,z1,z2,z1017,z4,z5]),(0,[z0,z1,z2,z3,z4,z1018]),(0,[z0,z1,z2,z1019,z4,z5]),(0,[z0,z44,z166,z3,z4,z208])]],
   [[(0,[z0,z1,z2,z13,z4,z307]),(0,[z761,z107,z2,z3,z4,z5]),(0,[z323,z1,z253,z3,z4,z5]),(0,[z185,z1,z2,z70,z4,z5]),(0,[z0,z134,z2,z3,z4,z8]),(0,[z256,z0,z2,z127,z4,z5]),(0,[z0,z1,z2,z3,z4,z1020]),(0,[z0,z1,z2,z381,z4,z509])],[(0,[z225,z0,z1,z2,z64,z5]),(0,[z0,z1,z2,z3,z4,z1021]),(0,[z109,z0,z1,z3,z4,z550])],[(0,[z0,z1,z2,z3,z4,z1022]),(0,[z1023,z0,z1,z2,z3,z4]),(0,[z0,z355,z2,z3,z4,z8]),(0,[z362,z1,z2,z3,z4,z312]),(0,[z0,z1,z2,z3,z4,z1024]),(0,[z0,z1,z2,z127,z241,z5]),(0,[z0,z1,z2,z371,z4,z299]),(0,[z211,z0,z2,z3,z4,z299]),(0,[z0,z570,z2,z3,z64,z5]),(0,[z228,z1,z2,z3,z64,z5]),(0,[z0,z2,z3,z4,z356,z8]),(0,[z0,z1,z481,z3,z4,z137])],[(0,[z0,z1,z2,z3,z1025,z5]),(0,[z1,z2,z3,z70,z203,z5]),(0,[z0,z1,z2,z3,z88,z10])],[(0,[z0,z1,z2,z3,z4,z1026]),(0,[z252,z1,z253,z3,z4,z8]),(0,[z0,z1,z2,z3,z1027,z5]),(0,[z0,z1,z2,z3,z4,z62]),(0,[z0,z1,z2,z156,z88,z5]),(0,[z0,z1,z2,z1028,z4,z5]),(0,[z0,z50,z2,z3,z64,z299]),(0,[z0,z1,z2,z146,z4,z164])],[(0,[z185,z1,z2,z70,z4,z8]),(0,[z0,z1,z2,z4,z741,z5])],[(0,[z0,z1,z2,z3,z4,z1029]),(0,[z1,z791,z15,z3,z4,z5]),(0,[z0,z1,z2,z1030,z4,z5]),(0,[z0,z1,z2,z3,z1031,z5]),(0,[z1032,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z1033,z4,z5]),(0,[z0,z1,z2,z3,z4,z1034]),(0,[z90,z0,z2,z3,z748,z5]),(0,[z0,z1,z2,z3,z4,z1035]),(0,[z0,z1,z2,z4,z785,z77])]],
   [[(0,[z0,z1,z2,z3,z1036,z5]),(0,[z0,z1,z2,z3,z4,z1037]),(0,[z0,z1,z2,z371,z4,z5])],[(0,[z1038,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z241,z5]),(0,[z0,z1,z1039,z3,z4,z5]),(0,[z0,z2,z3,z4,z299,z8]),(0,[z0,z1040,z2,z3,z4,z5])],[(0,[z0,z1,z1041,z3,z4,z5]),(0,[z0,z1,z1042,z3,z4,z5]),(0,[z1043,z0,z1,z3,z4,z5]),(0,[z0,z50,z2,z3,z64,z5]),(0,[z0,z1,z2,z3,z4,z1044]),(0,[z144,z0,z1,z2,z3,z613])],[(0,[z106,z761,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1045]),(0,[z681,z1,z2,z3,z154,z5]),(0,[z718,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z151,z241,z5]),(0,[z0,z1,z2,z492,z4,z77]),(0,[z1046,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z243,z10]),(0,[z0,z1,z2,z4,z1047,z5]),(0,[z17,z1,z2,z18,z4,z10]),(0,[z225,z0,z1,z2,z76,z5]),(0,[z0,z2,z3,z4,z388,z8]),(0,[z0,z508,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z4,z1048]),(0,[z318,z1,z2,z3,z154,z5]),(0,[z0,z1,z1042,z3,z4,z10]),(0,[z1043,z0,z1,z3,z4,z10]),(0,[z0,z1,z3,z919,z39,z5]),(0,[z228,z1,z2,z3,z76,z5])],[(0,[z673,z1,z2,z18,z4,z5]),(0,[z0,z1,z321,z3,z4,z411])],[(0,[z435,z1,z166,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1049])]],
   [[(0,[z362,z1,z2,z3,z4,z5]),(0,[z0,z1050,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1051]),(0,[z1,z2,z3,z804,z4,z5]),(0,[z211,z0,z2,z3,z4,z780]),(0,[z0,z1,z2,z143,z4,z300])],[(0,[z1052,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z5,z721])],[(0,[z0,z1,z2,z3,z4,z1053]),(0,[z94,z107,z2,z332,z4,z5]),(0,[z0,z2,z3,z4,z1054,z5]),(0,[z0,z1,z2,z20,z4,z312]),(0,[z0,z1,z1055,z3,z4,z5])],[(0,[z671,z0,z2,z3,z51,z5]),(0,[z0,z2,z3,z65,z51,z8])],[(0,[z0,z1,z457,z3,z4,z5]),(0,[z1056,z0,z1,z2,z4,z5]),(0,[z0,z1,z2,z3,z4,z496]),(1,[z0,z2,z840,z4,z5])],[(0,[z1057,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z371,z4,z509])],[(0,[z0,z260,z2,z127,z4,z5]),(0,[z47,z0,z2,z3,z51,z5])],[(0,[z0,z1,z2,z1058,z4,z5]),(0,[z500,z1,z2,z3,z4,z5]),(0,[z0,z1,z457,z3,z4,z10]),(0,[z0,z1,z2,z3,z4,z1059]),(0,[z0,z1,z2,z3,z4,z1060]),(0,[z0,z1,z2,z4,z7,z785])]],
   [[(0,[z1,z2,z3,z723,z154,z5]),(0,[z0,z1,z2,z3,z4,z1061])],[(0,[z94,z107,z2,z3,z4,z5]),(0,[z0,z44,z166,z3,z4,z62]),(0,[z0,z1,z2,z292,z4,z515])],[(0,[z0,z1,z2,z1062,z4,z5]),(0,[z262,z1,z2,z3,z27,z5]),(0,[z362,z1,z2,z3,z373,z5]),(0,[z36,z0,z1,z93,z4,z5])],[(0,[z0,z1,z533,z3,z4,z137]),(0,[z0,z1,z2,z3,z1063,z4]),(0,[z0,z1,z2,z3,z1064,z5]),(0,[z0,z1,z2,z3,z4,z350]),(0,[z0,z431,z2,z3,z4,z8])],[(0,[z150,z1,z2,z231,z154,z5]),(0,[z0,z600,z2,z3,z4,z8])],[(0,[z0,z1,z198,z3,z4,z8]),(0,[z0,z2,z3,z4,z876,z8]),(0,[z0,z2,z3,z4,z780,z8]),(0,[z9,z0,z1,z2,z190,z28])],[(0,[z0,z1,z2,z1065,z4,z5]),(0,[z669,z1,z2,z70,z4,z5]),(0,[z225,z0,z1,z2,z51,z5]),(0,[z0,z1,z2,z759,z4,z5]),(0,[z126,z0,z2,z127,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1066]),(0,[z435,z1,z45,z3,z4,z5]),(0,[z0,z1,z2,z3,z1067,z5]),(0,[z0,z1,z2,z3,z4,z1068]),(0,[z228,z1,z2,z3,z51,z5]),(0,[z0,z2,z3,z4,z438,z8])]],
   [[(0,[z0,z1,z95,z3,z4,z5]),(0,[z19,z0,z45,z3,z4,z5]),(0,[z126,z0,z2,z840,z4,z5]),(0,[z0,z1,z2,z124,z76,z5])],[(1,[z0,z2,z3,z4,z780]),(0,[z0,z1,z2,z3,z4,z1069])],[(0,[z326,z0,z2,z3,z4,z10])],[(0,[z1,z107,z95,z3,z4,z5]),(0,[z0,z1,z1070,z3,z4,z5]),(0,[z0,z1,z2,z3,z203,z10]),(0,[z0,z1,z2,z3,z181,z4]),(0,[z0,z1,z2,z3,z1071,z5]),(0,[z0,z1,z2,z20,z4,z10]),(0,[z126,z0,z2,z127,z4,z8]),(0,[z0,z2,z3,z4,z448,z8])],[(0,[z1,z761,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1072]),(0,[z0,z1,z2,z3,z1073,z5]),(0,[z0,z2,z3,z4,z51,z91]),(0,[z0,z50,z2,z381,z64,z5]),(0,[z0,z228,z1,z2,z28,z5])],[(0,[z0,z1,z95,z3,z4,z8]),(0,[z19,z0,z45,z3,z4,z8]),(0,[z0,z1,z2,z124,z76,z8]),(0,[z9,z0,z1,z2,z48,z28])],[(0,[z0,z1,z2,z3,z98,z8]),(0,[z106,z277,z2,z3,z4,z8]),(0,[z0,z1,z758,z3,z4,z10])],[(0,[z0,z2,z3,z4,z103,z10])]],
   [[(0,[z0,z1,z2,z124,z559,z5]),(0,[z0,z1,z2,z1074,z4,z5]),(0,[z0,z1,z2,z3,z162,z721])],[(0,[z0,z1,z2,z3,z4,z1075]),(0,[z0,z1,z604,z37,z4,z5]),(0,[z0,z628,z2,z3,z4,z8]),(0,[z0,z1,z2,z3,z1076,z5]),(0,[z0,z1,z2,z48,z3,z4])],[(0,[z0,z2,z3,z154,z51,z8]),(0,[z225,z0,z1,z2,z4,z10]),(0,[z0,z1,z2,z20,z373,z5]),(0,[z0,z1,z2,z3,z4,z1077]),(0,[z32,z0,z1,z3,z39,z5])],[],[(0,[z0,z1,z1078,z3,z4,z5]),(0,[z99,z1,z2,z3,z154,z5]),(0,[z0,z1,z2,z1079,z4,z5]),(0,[z0,z1,z2,z3,z4,z1080])],[(0,[z0,z1,z2,z1081,z4,z5]),(0,[z0,z1,z2,z4,z231,z10]),(0,[z362,z1,z2,z3,z4,z240]),(0,[z0,z50,z2,z371,z4,z8]),(0,[z0,z1,z2,z3,z4,z1082])],[(0,[z1083,z0,z1,z3,z4,z5]),(0,[z0,z1,z784,z3,z4,z5]),(0,[z0,z1,z2,z3,z160,z120])],[(0,[z0,z1,z364,z332,z4,z5]),(0,[z0,z1,z2,z1084,z4,z5]),(0,[z0,z1,z2,z3,z4,z1085]),(0,[z0,z1,z3,z4,z919,z5])]],
   [[(0,[z0,z1,z2,z3,z1086,z5]),(0,[z0,z1,z2,z3,z4,z1087]),(0,[z0,z1,z2,z194,z4,z8]),(0,[z228,z1,z2,z3,z28,z5])],[(0,[z0,z1,z2,z3,z4,z1088]),(0,[z0,z1,z2,z3,z4,z1089]),(0,[z0,z487,z2,z151,z4,z5]),(0,[z1083,z0,z1,z3,z4,z10]),(0,[z0,z1,z2,z1090,z3,z4])],[(0,[z0,z1,z1091,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1092]),(0,[z1093,z0,z1,z2,z3,z5]),(0,[z520,z0,z1,z93,z4,z5]),(0,[z0,z431,z2,z3,z4,z447])],[(0,[z0,z1,z95,z3,z4,z402]),(0,[z0,z1,z2,z3,z4,z1094]),(0,[z0,z1,z2,z3,z4,z1095]),(0,[z109,z0,z1,z3,z4,z58]),(0,[z1096,z1,z2,z3,z4,z5])],[(0,[z0,z1,z2,z1097,z4,z5]),(0,[z0,z1,z2,z3,z98,z402]),(0,[z0,z1,z2,z3,z4,z172]),(0,[z0,z132,z2,z151,z4,z496]),(0,[z0,z2,z3,z4,z8,z224])],[(0,[z0,z1,z2,z3,z4,z1098]),(0,[z0,z2,z3,z4,z1099,z5]),(0,[z0,z1,z2,z3,z4,z1100]),(0,[z0,z1,z2,z3,z88,z312])],[(0,[z0,z1,z364,z3,z4,z5]),(0,[z0,z1,z2,z13,z4,z5]),(0,[z0,z1,z2,z3,z1101,z4]),(0,[z0,z1,z2,z1102,z4,z5]),(0,[z0,z44,z166,z3,z4,z8]),(0,[z90,z0,z2,z3,z51,z176]),(0,[z0,z491,z2,z3,z4,z8]),(0,[z0,z1,z2,z146,z4,z7])],[(0,[z0,z1,z2,z1103,z4,z5]),(0,[z225,z0,z1,z2,z203,z5]),(0,[z0,z1,z2,z3,z4,z1104]),(0,[z145,z1,z2,z3,z27,z5])]],
   [[(0,[z692,z107,z2,z3,z4,z5]),(0,[z0,z1,z2,z4,z5,z1105]),(0,[z0,z1,z2,z3,z4,z1106]),(0,[z0,z431,z2,z3,z4,z162])],[(0,[z0,z1,z2,z3,z4,z1107]),(0,[z1,z2,z70,z154,z28,z5]),(0,[z0,z1,z2,z3,z723,z5]),(0,[z113,z1,z457,z3,z4,z138]),(0,[z0,z50,z2,z371,z64,z5]),(0,[z1108,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z721,z163])],[(0,[z0,z1,z2,z4,z1109,z5]),(0,[z0,z1,z1110,z3,z4,z5]),(0,[z1111,z1,z2,z3,z4,z5]),(0,[z0,z1,z2,z63,z76,z5])],[(0,[z0,z1,z2,z3,z1063,z203]),(0,[z0,z1,z2,z3,z4,z1112]),(0,[z0,z1,z2,z3,z582,z5]),(0,[z1113,z1,z2,z3,z4,z5])],[(0,[z1114,z1,z2,z3,z4,z5]),(0,[z0,z2,z499,z3,z4,z8]),(0,[z0,z1,z395,z2,z4,z300])],[(0,[z0,z1,z2,z1115,z4,z5]),(0,[z0,z1,z2,z3,z4,z1116]),(0,[z0,z1,z2,z18,z203,z5]),(0,[z0,z1,z2,z3,z1117,z4]),(0,[z233,z1,z2,z3,z4,z368]),(0,[z0,z1,z2,z20,z4,z240])],[(0,[z0,z1118,z2,z3,z4,z5]),(0,[z575,z1,z2,z70,z4,z5]),(0,[z0,z1,z2,z3,z4,z1119])],[(0,[z17,z1,z2,z3,z203,z5]),(0,[z145,z1,z2,z3,z204,z5]),(0,[z0,z1,z2,z3,z4,z1120]),(1,[z228,z1,z2,z28,z5]),(0,[z0,z1,z2,z3,z4,z1121])]],
   [[(0,[z145,z1,z2,z320,z4,z5]),(0,[z0,z1,z2,z3,z4,z1122]),(0,[z0,z1,z2,z1123,z4,z5]),(0,[z0,z1,z2,z3,z4,z1124])],[(0,[z0,z1,z2,z3,z4,z1125]),(0,[z0,z1,z2,z1126,z4,z5]),(0,[z0,z1,z2,z3,z1127,z5]),(0,[z0,z1,z2,z3,z4,z1128])],[(0,[z440,z1,z253,z3,z4,z5]),(0,[z0,z1,z1129,z3,z4,z5]),(0,[z0,z1,z2,z320,z154,z5]),(0,[z1130,z1,z2,z3,z4,z5]),(0,[z0,z562,z2,z151,z4,z5]),(0,[z0,z1,z2,z3,z4,z1131]),(0,[z556,z0,z2,z3,z4,z8]),(0,[z0,z1,z2,z1132,z4,z5])],[(0,[z0,z1,z2,z3,z4,z85]),(0,[z0,z1,z2,z3,z88,z5])],[(0,[z0,z1,z2,z3,z1133,z5])],[(0,[z0,z1,z2,z332,z243,z5]),(0,[z0,z1,z519,z3,z4,z137]),(0,[z144,z0,z1,z2,z3,z224]),(0,[z0,z1134,z2,z3,z4,z5])],[(0,[z0,z1,z2,z3,z4,z1135]),(0,[z150,z1,z2,z3,z181,z154])],[(0,[z0,z1,z2,z1136,z3,z4]),(0,[z0,z1,z2,z1137,z4,z5]),(0,[z0,z1,z2,z3,z4,z1138]),(0,[z0,z1,z1139,z2,z3,z4]),(0,[z0,z1,z2,z3,z4,z1140])]],
   [[(0,[z106,z277,z2,z3,z4,z85]),(0,[z0,z1,z1141,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1142])],[(0,[z0,z1,z364,z3,z4,z402]),(0,[z1,z791,z2,z3,z4,z5]),(0,[z0,z2,z1143,z3,z4,z5]),(0,[z0,z1144,z2,z3,z4,z5]),(0,[z0,z1,z2,z156,z4,z312]),(0,[z0,z1,z2,z3,z919,z5]),(0,[z0,z431,z2,z146,z3,z4])],[(0,[z0,z1,z2,z1145,z4,z5]),(0,[z0,z1,z2,z3,z4,z1146]),(0,[z9,z0,z1,z2,z28,z10]),(0,[z0,z1,z2,z3,z4,z1147])],[(0,[z0,z1,z2,z320,z4,z10]),(0,[z0,z1,z2,z3,z1148,z5]),(0,[z0,z1,z1149,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1150]),(0,[z144,z0,z1,z2,z3,z163])],[(0,[z0,z1,z2,z3,z243,z5]),(0,[z17,z1,z2,z18,z4,z5]),(0,[z1151,z1,z2,z3,z4,z5]),(0,[z0,z536,z2,z3,z4,z8])],[(0,[z0,z1,z2,z3,z1152,z5]),(0,[z0,z460,z2,z151,z4,z5])],[(0,[z0,z761,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z1153,z5]),(0,[z0,z1,z2,z3,z116,z10]),(0,[z0,z1,z2,z3,z4,z1154]),(0,[z1,z2,z3,z27,z723,z5]),(0,[z126,z0,z2,z127,z241,z5]),(0,[z0,z1,z2,z3,z210,z230])],[(0,[z0,z1,z2,z332,z4,z10]),(0,[z0,z1,z2,z3,z1155,z5]),(0,[z0,z344,z2,z3,z4,z8]),(0,[z0,z1156,z2,z3,z4,z5]),(0,[z0,z1,z2,z3,z4,z1157])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 532) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 532).take 534) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 1066).take 130) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1196)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [532, 534, 130] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 113).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 113).take 126).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 239).take 17).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [113, 126, 17] = true :=
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

end PEqualNP.Outside.L_meta_39255

theorem PEqualNP.Outside.L_meta_39255 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277074632 * 2 ^ 32 + 4276156608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277074632 * 2 ^ 32 + 4276156608) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_39255.solve