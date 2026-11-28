import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_36767

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
  Nat.testBit (4008373480 * 2 ^ 32 + 4008373376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x141403208824a095#64 ++ 0x67020941b042a366#64 ++ 0x7c7c1fe3f8ffe3ff#64 ++ 0xff933dc1fa63f3e7#64 : BitVec 256),
   (0xa888a04431084428#64 ++ 0xa708902c2918c855#64 ++ 0xff8fe0fc7f1dfc7f#64 ++ 0xffecd27e3d9ccc7f#64 : BitVec 256),
   (0x4d216d005a416902#64 ++ 0x08b0628b46170e83#64 ++ 0x7ff3ff007fe1ff8e#64 ++ 0xebb0e38fc61f0f87#64 : BitVec 256),
   (0x000256a900019243#64 ++ 0x483703d006e005a8#64 ++ 0x8003ffff8001fff3#64 ++ 0x4d7f03f007e00ff8#64 : BitVec 256),
   (0x000398d264900002#64 ++ 0x883df40007ad5000#64 ++ 0x0003fffffffe0003#64 ++ 0x8e3ffc0007fff000#64 : BitVec 256),
   (0x7240000000000003#64 ++ 0xd03ffff6d8000000#64 ++ 0xfffc000000000003#64 ++ 0xf03ffffff8000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [2, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.and, [8, 1]⟩, ⟨.or, [9, 3]⟩, ⟨.or, [8, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [13, 10]⟩, ⟨.and, [11, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003ffff8001fff3 0x4d7f03f007e00ff8

def z1 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003fffffffe0003 0x8e3ffc0007fff000

def z2 : W := mkw 0x0003dcdb64911242 0x883df69007ad5488 0x8003e01c07001c00 0x006cc230059c0c18

def z3 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c1fe3f8ffe3ff 0xff933dc1fa63f3e7

def z4 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3ff007fe1ff8e 0xebb0e38fc61f0f87

def z5 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc000000000003 0xf03ffffff8000000

def z6 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8fe0fc7f1dfc7f 0xffecd27e3d9ccc7f

def z7 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000000001fc70 0x4140027000000c78

def z8 : W := mkw 0x141447298825b2d5 0x67020bd1b042a7ee 0xfc7c00000001fffc 0x71c003f1f8000fff

def z9 : W := mkw 0x4921280052404900 0x0080600a40150801 0x0380000007000000 0x0000c00e001c0000

def z10 : W := mkw 0x5243189244900003 0x58376fd2d6a51000 0x00701f0380e20000 0x00132d81c2633000

def z11 : W := mkw 0x041403208824a094 0x270000012042a366 0x00001fe3f8ffe3fc 0x0f8000000263f3e7

def z12 : W := mkw 0x8888a04431084428 0x270000082118c855 0x0003e0fc7f1dfc7c 0x0fc00000059ccc7f

def z13 : W := mkw 0xeda9a9447b486d28 0xa788f02f691fca57 0x7ffc00007ffc000c 0xb280f00ff81fc007

def z14 : W := mkw 0xeda9ed447b496d2a 0xafb8f2af6f1fced7 0xfffffffc7ffdffff 0xfffcf3ffff9fcfff

def z15 : W := mkw 0x0000022000008001 0x4002014000400120 0x00001fe38001e3f3 0x4d1301c0026003e0

def z16 : W := mkw 0x141657a98825b2d7 0x6f370bd1b6e2a7ee 0xfc7ffffff8ffffff 0xffff3ff1ffe3ffff

def z17 : W := mkw 0x0001885264900000 0x8008f400010d5000 0x00001fe3fffe0003 0x8e13fc00027ff000

def z18 : W := mkw 0x0002548900011242 0x0835029006a00488 0x8003e01c00001c00 0x006c023005800c18

def z19 : W := mkw 0x7240000000000001 0xd00afd66d8000000 0x7ffc000000000003 0xf013fdcff8000000

def z20 : W := mkw 0x4d2065001a416900 0x0080028b40120e83 0x7ff000000001ff8c 0x6180038fc0000f87

def z21 : W := mkw 0x724256a900019243 0xd83ffff6dee005a8 0xffffffff8001fff3 0xfd7fffffffe00ff8

def z22 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x00001f0380000380 0x0013018002600380

def z23 : W := mkw 0x5d3467209a65e995 0x67820bcbf052afe7 0x7ffc00000001fffc 0x718003cff8000fe7

def z24 : W := mkw 0x765403208824a097 0xd03ffff7d8422322 0xfffc1f0380e20383 0xf03ffffffa633380

def z25 : W := mkw 0x1014022080248095 0x67020940b040a164 0x7c0c00e3f81fe07f 0xff831c403860f067

def z26 : W := mkw 0x0002108000000002 0x0835000006a00000 0x0003ffff80000003 0x0c3f000007e00000

def z27 : W := mkw 0xa88ab0c43108442a 0xaf3d902c2fb8c855 0xff8fffffff1dfc7f 0xffffd27e3ffccc7f

def z28 : W := mkw 0x0000000000000000 0x2700000020008044 0xfc0fe0fc781dfc7f 0xffec12703d80cc7f

def z29 : W := mkw 0x0002108000000002 0x883df40006a00000 0x0003ffff80000003 0x8c3ffc0007e00000

def z30 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001fe3f8fe0003 0x8e133c000263f000

def z31 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3e0000701ff8c 0x61a0c38fc41c0f87

def z32 : W := mkw 0xa88bb8d675984428 0xaf08902c2fbdd855 0xff8ffffffffffc7f 0xffecd27e3ffffc7f

def z33 : W := mkw 0x1000000000000001 0x4002094090000000 0x7c7c000000000003 0xf0133dc1f8000000

def z34 : W := mkw 0x765403208824a097 0xf73ffff7f842a366 0xfffc1fe3f8ffe3ff 0xffbffffffa63f3e7

def z35 : W := mkw 0x141403208824a095 0x4002094190422322 0x00701f0380e20380 0x00132d81c2633380

def z36 : W := mkw 0xbc9ca364b92ce4bd 0xe70a996db95aeb77 0xffffffffffffffff 0xffffffffffffffff

def z37 : W := mkw 0x1d356f20da65e995 0x6f820949b657afe7 0x7c7fffe3ffffffff 0xff933dc1fe7fffe7

def z38 : W := mkw 0xfac8200411084429 0x77020bfef8108855 0xfffc00000001fc7c 0x71c003fff8000c7f

def z39 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e00001e073 0x4d00004000000060

def z40 : W := mkw 0x000290d224900000 0x800d940001a85000 0x000000ff801e0001 0x040f1c0001e0f000

def z41 : W := mkw 0x000398d264900000 0x0800000007ad5000 0x0003fffffffe0000 0x0e00000007fff000

def z42 : W := mkw 0xa88bb8d67598442a 0xaf3df42c2fbdd855 0xff8ffffffffffc7f 0xfffffe7e3ffffc7f

def z43 : W := mkw 0xbc9c2324992ce4bd 0x6702096db852ab77 0xfffc1fe3f8ffffff 0xffd33ffffa63ffff

def z44 : W := mkw 0x1014022080248095 0x67020940b040a164 0x7c7c00e3801e0073 0xf4133dc1f860f060

def z45 : W := mkw 0x0800200010004000 0x0000000800100801 0x7f83e0007f01fc0e 0xeba0c20e041c0c07

def z46 : W := mkw 0xa088804421080428 0xa70890242908c054 0x800c00fc001c0071 0x144c10703980c078

def z47 : W := mkw 0x45214d004a412902 0x08b0628346070682 0x7ff01f0000e00382 0xe030e38fc2030380

def z48 : W := mkw 0x0003defb64919243 0xc83ff7d007ed55a8 0x8003fffffffffff3 0xcf7ffff007fffff8

def z49 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0x7f8c00007f1c000c 0xb280d00e381cc007

def z50 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003e01c7ffe0000 0x822cfc00059ff000

def z51 : W := mkw 0x7240000000000000 0x9008fc26d8000000 0x7ffc000000000000 0xb000fc0ff8000000

def z52 : W := mkw 0x7240000000000001 0x50020bf6d8000000 0xfffc000000000000 0x700003fff8000000

def z53 : W := mkw 0x724256a900019243 0x58370bf6dee005a8 0xffffffff8001fff3 0x7d7f03ffffe00ff8

def z54 : W := mkw 0x2000000000000000 0x0000002408000000 0xff8c000000000000 0x7000027e38000000

def z55 : W := mkw 0x724398d264900003 0xd83ffff6dfad5000 0xfffffffffffe0003 0xfe3ffffffffff000

def z56 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc1fe3f8fe0003 0xfe3ffffffa63f000

def z57 : W := mkw 0x0003189244900002 0x0835640006a51000 0x00001f0380e20000 0x00132c0002633000

def z58 : W := mkw 0x0400010008002000 0x0000000100020202 0x7c701f0078e1e38e 0xeb902181c2030387

def z59 : W := mkw 0x4920640012414900 0x0080028a40100c81 0x0380000000001c00 0x0000020e00000c00

def z60 : W := mkw 0x324290d224900001 0xd00f9d7499a85000 0x800c00ff801e0001 0x140f1c7039e0f000

def z61 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0x7f8fe0fc7f1c000f 0xbeacd00e3d9cc007

def z62 : W := mkw 0xa888a2643108c429 0xe70a916c2958c975 0xff8fffffff1dffff 0xffffd3fe3ffccfff

def z63 : W := mkw 0x0000440000010002 0x0830028006000480 0x0003ff000001ff82 0x4930038006000f80

def z64 : W := mkw 0x000398d264900000 0x800df40001ad5000 0x000000fffffe0001 0x860ffc0001fff000

def z65 : W := mkw 0x0001080040000002 0x0830600006050000 0x0003ff007fe00002 0x8a30e000061f0000

def z66 : W := mkw 0x0000000000000000 0x0000000000000000 0x0003e0007f000002 0x8a20c000041c0000

def z67 : W := mkw 0x4000000000000002 0x0030628240000000 0x7ff0000000000002 0xe030e38fc0000000

def z68 : W := mkw 0x041403208824a094 0x270000012042a366 0x00001fe3f8ffe3ff 0x8f933c000263f3e7

def z69 : W := mkw 0x7640010008002003 0xd03ffff7d8020202 0xfffc1f0078e1e38f 0xfbbffffffa030387

def z70 : W := mkw 0x0002548900011242 0x0835029006a00488 0x8003ff1c0001ff82 0x497c03b007800f98

def z71 : W := mkw 0x0800200010004000 0x0000000800100801 0x0383e00007001c00 0x0020c20e041c0c00

def z72 : W := mkw 0x100256a900019243 0x48370bd096e005a8 0xfc7fffff8001fff3 0xfd7f3ff1ffe00ff8

def z73 : W := mkw 0x4400010008002002 0x0030628340020202 0x7ff01f0078e1e38e 0xebb0e38fc2030387

def z74 : W := mkw 0x1414010088242094 0x27000801b002a246 0x7c7c000078fe000c 0xb2803c01f803f007

def z75 : W := mkw 0x0d23fdd27ed16900 0x0880000907bf5e83 0x0003ffffffffff8c 0x0f80000007ffff87

def z76 : W := mkw 0x4d237d805a416902 0x08b5628b46b70e83 0x7ff3ffffffe1ff8f 0xefbfe38fc7ff0f87

def z77 : W := mkw 0x4d237fa95a41fb43 0x48b763db46f70fab 0xfff3ffffffe1ffff 0xefffe3ffc7ff0fff

def z78 : W := mkw 0x041403208824a095 0x670201412042a366 0x00001fe3f8ffe3ff 0x4f9301c00263f3e7

def z79 : W := mkw 0x0002d6fb24919243 0xc83f97d007e855a8 0x8003ffff801ffff3 0x4d7f1ff007e0fff8

def z80 : W := mkw 0xa08b98d66598042a 0xaf3df4242fadd054 0x800ffffffffe0073 0x9e7ffc703ffff078

def z81 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003fffff8fffff3 0xcf7f3ff007e3fff8

def z82 : W := mkw 0x00035ebb44919243 0x483767d006e515a8 0x8003ffff80e3fff3 0x4d7f2ff007e33ff8

def z83 : W := mkw 0xa888a04431084428 0x8008902c09184811 0x8383e01c07001c00 0x006cc23e059c0c18

def z84 : W := mkw 0x000256a900019241 0x4807015006e005a8 0x8003ffff8001fff1 0x0d4f007007e00ff8

def z85 : W := mkw 0x7243defb64919243 0xd83ffff6dfed55a8 0xfffffffffffffff3 0xff7ffffffffffff8

def z86 : W := mkw 0x0800200010004000 0x0000000800100801 0x7f8000007f00000c 0xa280c00e001c0007

def z87 : W := mkw 0x1014022080248095 0x67020940b040a164 0x000c1fe3f8fe0073 0x9e133c403a63f060

def z88 : W := mkw 0x7f616d005a416903 0x58b26bffde170e83 0xffffff007fe1ff8e 0xfbb0e3fffe1f0f87

def z89 : W := mkw 0x0000000000000000 0x0000000000000000 0x8003e0fc0001fc73 0x4d6c027005800c78

def z90 : W := mkw 0x0003dcdb64911242 0x883df69007ad5488 0x8003fffffffe1c03 0x8e7ffe3007fffc18

def z91 : W := mkw 0x0000462900019241 0x400203d0004005a8 0x8003e0fc0001fff3 0x4d6c03f005800ff8

def z92 : W := mkw 0xa888a0443108442b 0xe73f93fc2918c855 0xff8fe0fc7f1dfc7f 0xffffd3fe3d9ccc7f

def z93 : W := mkw 0x0003189244900002 0x0835640006a51000 0x0003ffff80e20003 0x0c3f2c0007e33000

def z94 : W := mkw 0x7f616d005a416903 0xd8bfffffde170e83 0xffffff007fe1ff8f 0xfbbffffffe1f0f87

def z95 : W := mkw 0x0001885264900000 0x8008f400010d5000 0x000000007ffe0000 0x8200fc00001ff000

def z96 : W := mkw 0x7f616d005a416902 0x98b8feafde170e83 0x7fffff007fe1ff8e 0xfbb0ff8ffe1f0f87

def z97 : W := mkw 0x0000804020000000 0x8008900001084000 0x0003e0fc7f1c0003 0x8e2cd000059cc000

def z98 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c00000001e3fc 0x718001c1f80003e7

def z99 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x03f3ff0007e01f80 0x0030e38fc61f0f80

def z100 : W := mkw 0x7242108000000003 0xd83ffff6dea00000 0xffffffff80000003 0xfc3fffffffe00000

def z101 : W := mkw 0xa88af6ed3109d66b 0xef3f93fc2ff8cdfd 0xff8fffffff1dffff 0xffffd3fe3ffccfff

def z102 : W := mkw 0x0000000000000002 0x803df40000000000 0x0000000000000003 0x803ffc0000000000

def z103 : W := mkw 0x5d356f20da65e997 0x6fb26bcbf657afe7 0x7fffffe3ffffffff 0xffb3ffcffe7fffe7

def z104 : W := mkw 0x8888a04431084428 0x270000082118c855 0x7c0fe0fc7f1dfc7f 0xffc010403d9ccc7f

def z105 : W := mkw 0x000212a900009241 0x4007015000e00128 0x8003e0ff8001fc73 0x4d6f027005e00c78

def z106 : W := mkw 0x4d2129005a406902 0x08b0600b46170a03 0x7ff3ff007fe0000e 0xaab0e00fc61f0007

def z107 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c1fe3f8ffe3fc 0x7f8001c1fa63f3e7

def z108 : W := mkw 0x0000000000000000 0x0000000000000000 0x7c0c000000000003 0xf000104038000000

def z109 : W := mkw 0x6240000000000003 0xd03ff7f648000000 0x8380000000000003 0x403fc3fe00000000

def z110 : W := mkw 0xa888a04431084428 0x8008902c09184811 0x8383e0fc7f1c1c03 0x8e6cd23e059ccc18

def z111 : W := mkw 0x524398d264900003 0xd83fffd2d7ad5000 0x0073fffffffe0003 0x8e3ffd81c7fff000

def z112 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z113 : W := mkw 0x0000000000000000 0x8008f40000000000 0x0000000000000000 0x8000fc0000000000

def z114 : W := mkw 0x000212a900009241 0x4007015000e00128 0x0000000380000000 0x0003000000600000

def z115 : W := mkw 0x000398d264900002 0x0835000007ad5000 0x0003fffffffe0003 0x0e3f000007fff000

def z116 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc000000000000 0x702cc3fff8000000

def z117 : W := mkw 0x0401090048002002 0x0830600106070202 0x7c73ff007fe1e38e 0xebb0e181c61f0387

def z118 : W := mkw 0x041403208824a094 0x270000012042a366 0x000000000001e3fc 0x01800000000003e7

def z119 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c1f0078e1e3fe 0xfb9021c1fa0303e7

def z120 : W := mkw 0x14179bf2ecb4a095 0x6f020941b7eff366 0x7c7fffffffffe3ff 0xff933dc1fffff3e7

def z121 : W := mkw 0x3240000000000001 0x5002097498000000 0x800c000000000000 0x1000007038000000

def z122 : W := mkw 0xa888200411084428 0x2700002c28108855 0xff8c00000001fc7c 0x71c0027e38000c7f

def z123 : W := mkw 0x1014022080248095 0x67020940b040a164 0x000c00e3801e0071 0x14031c403860f060

def z124 : W := mkw 0x1014022080248095 0x4002094090402120 0x0000000380020000 0x00030c0000603000

def z125 : W := mkw 0x0c00210018006000 0x0000000900120a03 0x7ff3ff007fe1ff8e 0xebb0e38fc61f0f87

def z126 : W := mkw 0x000292fb24909241 0xc00f955001e85128 0x800000ff801e0071 0x044f1c7001e0f078

def z127 : W := mkw 0x000290d224900000 0x800d940001a85000 0x0000001c00000000 0x000c000001800000

def z128 : W := mkw 0x0000000000000002 0x803df40000000000 0x00001fe3f8fe0003 0x8e3ffc000263f000

def z129 : W := mkw 0x000212a900009241 0x4007015000e00128 0x800000ff80000071 0x044f007001e00078

def z130 : W := mkw 0x4d2129005a406900 0x0080600b40170a03 0x7ff000007fe0000c 0xa280e00fc01f0007

def z131 : W := mkw 0x49216c0052414902 0x08b0628a46150c81 0x0383e00007001c00 0x0020c20e041c0c00

def z132 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003fffffffe0000 0x0e2cc00007fff000

def z133 : W := mkw 0xa888a04431084428 0x8008902c09184811 0xff8fe01c07001c03 0xf06cd27e3d9c0c18

def z134 : W := mkw 0xbac8a04431084429 0xf70f9d7cb918c855 0xff8fe0fc7f1dfc7f 0xffefde7e3d9ccc7f

def z135 : W := mkw 0x0000440000010002 0x0830028006000480 0x8003fffc0001fff3 0x4d7c03f007800ff8

def z136 : W := mkw 0x141403208824a095 0x4002094190422322 0x00701fe3f8fe0383 0x8e133d81c263f380

def z137 : W := mkw 0x4000000000000002 0x0030628240000000 0x0380000000000000 0x0020c20e00000000

def z138 : W := mkw 0x0002548900011242 0x0835029006a00488 0x8003e0fc0001fc73 0x4d6c027005800c78

def z139 : W := mkw 0x2000000000000000 0x8008902408000000 0x800c000000000001 0x100c107038000000

def z140 : W := mkw 0x4d23fdd27ed16902 0x88bdf68b47bf5e83 0x7ff3ffffffffff8f 0xefbfff8fc7ffff87

def z141 : W := mkw 0x000398d264900000 0x0800000007ad5000 0x0003fffffffe0003 0x8e133c0007fff000

def z142 : W := mkw 0x141447208825a097 0x6f320bc1b642a7e6 0x7c7fffe3f8ffffff 0xffb33fc1fe63ffe7

def z143 : W := mkw 0xfac8a04431084428 0xb708fc2ef918c855 0xffffe0fc7f1dfc7f 0xffecfe7ffd9ccc7f

def z144 : W := mkw 0x7240462900019243 0xd03ffff6d84005a8 0xfffc00000001fff3 0xf17ffffff8000ff8

def z145 : W := mkw 0x0002548900011242 0x0835029006a00488 0x0000000000000000 0x0000000000000000

def z146 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x8003fffffffffc73 0xcf7ffe7007fffc78

def z147 : W := mkw 0x14179bf2ecb4a097 0xef3ffd41b7eff366 0x7c7fffffffffe3ff 0xffbffdc1fffff3e7

def z148 : W := mkw 0x04179bf2ecb4a096 0xaf3df40127eff366 0x0003ffffffffe3ff 0x8fbffc0007fff3e7

def z149 : W := mkw 0x4d216d005a416900 0x0080628b40170e83 0x7ff000007fe1ff8c 0xe380e38fc01f0f87

def z150 : W := mkw 0x4000000000000000 0x0000600240000000 0x7ff0000000000000 0xa000e00fc0000000

def z151 : W := mkw 0x4d216d005a416900 0x0880028b46170e83 0x7ff3ff007fe1ff8c 0x6b80038fc61f0f87

def z152 : W := mkw 0x1c1423209824e095 0x67020949b052ab67 0x7fffffe3ffffffff 0xffb3ffcffe7fffe7

def z153 : W := mkw 0x0000462900019241 0x400203d0004005a8 0x800000000001fff0 0x414003f000000ff8

def z154 : W := mkw 0x0001885264900000 0x8008f400010d5000 0x0000000007000000 0x0000c000001c0000

def z155 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8c00007f1c000f 0xf2acd27e381cc007

def z156 : W := mkw 0x8888a04431084428 0x270000082118c855 0x8003e0fc7f1dfc7f 0x4fec0270059ccc7f

def z157 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0xfff3fffc7fe1ffff 0xeffce3ffc79f0fff

def z158 : W := mkw 0x6240000000000002 0x903df6b648000000 0x8380000000000000 0x002cc23e00000000

def z159 : W := mkw 0x0000022000008001 0x6702014020408164 0x7c0c1fe3f81de3ff 0xff9311c03a60c3e7

def z160 : W := mkw 0x0000000000000002 0x0035029000000000 0x8000000000000000 0x002c023000000000

def z161 : W := mkw 0x000398d264900000 0x8808f40007ad5000 0x0003fffffffe0000 0x8e00fc0007fff000

def z162 : W := mkw 0x000256a900019240 0x0800000006e005a8 0x0003ffff8001fff0 0x0d40000007e00ff8

def z163 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003e0fc7f1c0003 0x8e2cd000059cc000

def z164 : W := mkw 0x7240000000000001 0xd00ffd76d8000000 0xfffc000000000001 0xb00ffc7ff8000000

def z165 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8c00fc001dfc7d 0x75cc127e3980cc7f

def z166 : W := mkw 0x0003defb64919243 0x483703d007ed55a8 0x8003fffffffffff3 0x4f7f03f007fffff8

def z167 : W := mkw 0xa888200411084428 0xa708902c28108855 0xff8c00000001fc7f 0xf1ecd27e38000c7f

def z168 : W := mkw 0x7240000000000003 0x50376ff6d8000000 0xfffc000000000000 0x70132ffff8000000

def z169 : W := mkw 0x0001080040000002 0x0830600006050000 0x0003ffe3fffe0003 0x8e33fc00067ff000

def z170 : W := mkw 0xa88bb8d67598442a 0x883df42c0fbd5811 0x8383fffffffe1c03 0x8e7ffe3e07fffc18

def z171 : W := mkw 0x4000000000000002 0x0030628240000000 0x0070000000000000 0x00102181c0000000

def z172 : W := mkw 0x4d237d895a417b42 0x08b5629b46b70e8b 0xfff3ff1c7fe1ff8e 0xebfce3bfc79f0f9f

def z173 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003e01c0001fff0 0x416c03f005800ff8

def z174 : W := mkw 0x0000000000000002 0x803df40000000000 0x0000000000000000 0x002cc00000000000

def z175 : W := mkw 0x0000440000010003 0x483703d006000480 0x8003ff000001ff83 0x493f03f006000f80

def z176 : W := mkw 0x4001080040000002 0x0830628246050000 0x7ff3ff007fe00002 0xea30e38fc61f0000

def z177 : W := mkw 0xbc9c2324992ce4bd 0x6702096db852ab77 0xfffc00000001fffc 0x71c003fff8000fff

def z178 : W := mkw 0x724212a900009243 0xd03ffff6d8e00128 0xfffc00ff80000073 0xf47ffffff9e00078

def z179 : W := mkw 0x0000462000018003 0x483203c0064005a0 0x0003ffe38001fff3 0x4d3303c006600fe0

def z180 : W := mkw 0x041403208824a094 0x270000012042a366 0x7c701fe3f8ffe3fe 0xef902181c263f3e7

def z181 : W := mkw 0x0000000000000003 0x403703d000000000 0x8003e0fc0001fc73 0x4d7f03f005800c78

def z182 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000078fe0000 0x82003c000003f000

def z183 : W := mkw 0x7240000000000003 0x50326bf6d8000000 0xfffc000000000002 0xf030e3fff8000000

def z184 : W := mkw 0x4d237fa95a41fb43 0x48b763db46f70fab 0x7ff3ff03ffe1ff8e 0xebb3e38fc67f0f87

def z185 : W := mkw 0x624256a900019243 0xd83ff7f64ee005a8 0x8383ffff8001fff3 0x4d7fc3fe07e00ff8

def z186 : W := mkw 0x0000000000000003 0x403703d000000000 0x0000000000000000 0x0013018000000000

def z187 : W := mkw 0x1000022000008001 0x4002094090400120 0x7c7c1fe38001e3f3 0xfd133dc1fa6003e0

def z188 : W := mkw 0x3240000000000001 0xd00f9d7498000000 0x800c000000000001 0x100f1c7038000000

def z189 : W := mkw 0x9c9ca364b92ce4bd 0x67020949b15aeb77 0x7c7fffffffffffff 0xffd33dc1ffffffff

def z190 : W := mkw 0x4d2065001a416902 0x00b0628b40120e83 0x7ff000000001ff8e 0xe1b0e38fc0000f87

def z191 : W := mkw 0x4d237d925ed16902 0x08b5668b46b71e83 0x7ff3ff03ffe3ff8e 0xebb3ef8fc67f3f87

def z192 : W := mkw 0x7240022000008003 0xd03ffff6d8400120 0xfffc1fe38001e3f3 0xfd3ffffffa6003e0

def z193 : W := mkw 0x000290d224900002 0x883d940007a85000 0x0003ffff801e0003 0x0c3f1c0007e0f000

def z194 : W := mkw 0xe9a9ec4473494d2a 0xafb8f2ae6f1dccd5 0xff8fe0fc7f1dfc7f 0xffecd27e3d9ccc7f

def z195 : W := mkw 0x45235fa94a41bb43 0x48b763d346e707aa 0x8073ffff80e1fff3 0x4d7f23f1c7e30ff8

def z196 : W := mkw 0x45214d004a412902 0x08b0628346070682 0x00701f0000e00380 0x00102181c2030380

def z197 : W := mkw 0x041403208824a094 0x270000012042a366 0x7c0c1fe3f8ffe3ff 0xff8010403a63f3e7

def z198 : W := mkw 0x000256a900019241 0x400703d000e005a8 0x800000ff8001fff1 0x454f03f001e00ff8

def z199 : W := mkw 0x0d216d005a416900 0x0880000906170e83 0x0003ff007fe1ff8c 0x0b800000061f0f87

def z200 : W := mkw 0x7240000000000001 0xd00a9bf6d8000000 0xfffc000000000003 0xf02cd3fff8000000

def z201 : W := mkw 0xa88af6ed3109d668 0xaf08902c2ff8cdfd 0xff8fffffff1dffff 0xffecd27e3ffccfff

def z202 : W := mkw 0x2000000000000000 0x8008902408000000 0xff8c000000000003 0xf02cd27e38000000

def z203 : W := mkw 0x45214d004a412902 0x08b0628346070682 0x0073ff007fe00382 0x8a30e181c61f0380

def z204 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0x800fe0fc7f1dfc7d 0x1fcc10703d9ccc7f

def z205 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3ffe3ffffff8f 0xefb3ff8fc67fff87

def z206 : W := mkw 0x0001080040000002 0x0830600006050000 0x0003e00007000000 0x0020c000041c0000

def z207 : W := mkw 0x0001080040000002 0x883df40006050000 0x0003ff007fe00003 0x8a3ffc00061f0000

def z208 : W := mkw 0x0001885264900000 0x00000000010d5000 0x000000007ffe0000 0x02000000001ff000

def z209 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e3801e0001 0x04031c000060f000

def z210 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c00e3801fe3fd 0x75831dc1f860f3e7

def z211 : W := mkw 0x0003dcd264910002 0x883df68007ad5480 0x0003ffffffffff83 0xcf3fff8007ffff80

def z212 : W := mkw 0x4d2021001a406900 0x0080000b40120a03 0x7ff000000000000c 0x2080000fc0000007

def z213 : W := mkw 0x0002548000010002 0x0835028006a00480 0x0003ffff8001ff83 0x4d3f038007e00f80

def z214 : W := mkw 0x724290d224900003 0xd03ffff6d9a85000 0xfffc00ff801e0003 0xf43ffffff9e0f000

def z215 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c00000001e3ff 0xf1933dc1f80003e7

def z216 : W := mkw 0x0000000000000000 0x0000000000000000 0x7c70000000000002 0xe0102181c0000000

def z217 : W := mkw 0xfedca364b92ce4bf 0xf73ffffff95aeb77 0xffffffffffffffff 0xffffffffffffffff

def z218 : W := mkw 0x0d356f20da65e994 0x2f8000092657afe7 0x0003ffe3fffffffc 0x0f800000067fffe7

def z219 : W := mkw 0x141403208824a095 0x67020941b042a366 0x00701fe3f8ffe3fc 0x0f932d81c263f3e7

def z220 : W := mkw 0x888bb8d675984428 0x2f00000827bdd855 0x0003fffffffffc7c 0x0fc0000007fffc7f

def z221 : W := mkw 0xfac8a0443108442b 0xf73ffffef918c855 0xffffe0fc7f1dfc7f 0xfffffffffd9ccc7f

def z222 : W := mkw 0x0000000000000003 0x403703d000000000 0x8000000000000003 0x403f03f000000000

def z223 : W := mkw 0x2000000000000003 0xc03f93f408000000 0xff8c000000000003 0xf03fd3fe38000000

def z224 : W := mkw 0x1414010088242094 0x27000801b002a246 0x7c7c00e078ffe07f 0xff803c41f803f067

def z225 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003e01c07000000 0x002cc000059c0000

def z226 : W := mkw 0x0800640010014002 0x0830028806100c81 0x7f83ff007f01ff8e 0xebb0c38e061c0f87

def z227 : W := mkw 0x0000000000000000 0x0000000000000000 0x7c0000007801e00e 0xeb80000000000007

def z228 : W := mkw 0x00014c0040010002 0x0830628006050480 0x0003ff007fe1ff82 0xcb30e380061f0f80

def z229 : W := mkw 0x040003200800a001 0x4002014100420322 0x7c701fe3f8e1e3ff 0xef9321c1c26303e7

def z230 : W := mkw 0x6240000000000000 0x100002b648000000 0x8380000000000000 0x0000023e00000000

def z231 : W := mkw 0x0000804020000000 0x8008900001084000 0x0003e01c07000000 0x002cc000059c0000

def z232 : W := mkw 0x765403208824a097 0xf73ffff7f842a366 0xfffc00000001e3ff 0xf1bffffff80003e7

def z233 : W := mkw 0x0003189244900002 0x0835640006a51000 0x00001fe3f8fe0003 0x8e133c000263f000

def z234 : W := mkw 0x4d21a9527ed06900 0x8088f40b411f5a03 0x7ff000007ffe000c 0xa280fc0fc01ff007

def z235 : W := mkw 0x14148360a824a095 0xe70a9941b14ae366 0x7c7fffffffffe3ff 0xffbffdc1fffff3e7

def z236 : W := mkw 0x0000804020000000 0x8008900001084000 0x0003fffffffe0003 0x8e3ffc0007fff000

def z237 : W := mkw 0x141403208824a095 0x67020941b042a366 0x000c1fe3f8ffe3fd 0x1f831c403a63f3e7

def z238 : W := mkw 0xa888e66d3109d669 0xe70a93fc2958cdfd 0xff8fe0fc7f1dffff 0xffecd3fe3d9ccfff

def z239 : W := mkw 0x000212a000008003 0x4837014006e00120 0x0003ffff8001e3f3 0x4d3f01c007e003e0

def z240 : W := mkw 0x7f6065001a416903 0xd0bfffffd8120e83 0xfffc00000001ff8f 0xf1bffffff8000f87

def z241 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003e0ff871e0001 0x042fdc0005fcf000

def z242 : W := mkw 0x0002548900011243 0x483703d006a00488 0x8003e01c00001c03 0x407f03f005800c18

def z243 : W := mkw 0x0000000000000000 0x2700000020008044 0x7c0c00e0781de07f 0xff8010403800c067

def z244 : W := mkw 0x6240000000000002 0x903df6b648000000 0xff8c000000000003 0xf02cd27e38000000

def z245 : W := mkw 0x4d216f295a41fb43 0x48b263db46570fab 0xfff3ff007fe1fffe 0xebf0e3ffc61f0fff

def z246 : W := mkw 0x765403208824a095 0x77020bf7f842a366 0xfffc00000001e3fc 0x718003fff80003e7

def z247 : W := mkw 0x7240000000000003 0xf73ffff6f8008044 0xfffc00e0781de07f 0xffbffffff800c067

def z248 : W := mkw 0x141403208824a095 0x67020941b042a366 0x007c1fe380fe03f1 0x14133dc1fa63f3e0

def z249 : W := mkw 0x7240000000000000 0x10000826d8000000 0x7ffc000000000000 0x3000000ff8000000

def z250 : W := mkw 0x4d23b9d27ed06902 0x88bdf40b47bf5a03 0x7ff3fffffffe000f 0xaebffc0fc7fff007

def z251 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff01f007fe0038c 0xa290e18fc21f0387

def z252 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e0781c0003 0x8e0010000000c000

def z253 : W := mkw 0x4000000000000002 0x803df68240000000 0x7ff0000000000003 0xe03fff8fc0000000

def z254 : W := mkw 0x0000000000000000 0x800d940000000000 0x0000000000000001 0x000f1c0000000000

def z255 : W := mkw 0x8888200411084428 0x2700000820108855 0x000000000001fc7c 0x01c0000000000c7f

def z256 : W := mkw 0x0000000000000000 0x2700000020008044 0x000000e0781de07c 0x0f8000000000c067

def z257 : W := mkw 0x7242548900011243 0xd83ffff6dea00488 0xffffe01c00001c03 0xf07ffffffd800c18

def z258 : W := mkw 0x6242548900011242 0x983df6b64ea00488 0x8383e01c00001c00 0x006cc23e05800c18

def z259 : W := mkw 0x7240000000000001 0xd00f9ff6d8000000 0xfffc000000000001 0x700f1ffff8000000

def z260 : W := mkw 0x000256a900019241 0x480203d006e005a8 0x8003ffff8001fff0 0x4d4003f007e00ff8

def z261 : W := mkw 0x49237ea95241db43 0x48b763da46f50da9 0x8383ffff8701fff3 0x4d7fc3fe07fc0ff8

def z262 : W := mkw 0x7f6065001a416901 0x50820bffd8120e83 0xfffc00000001ff8c 0x718003fff8000f87

def z263 : W := mkw 0x724398d264900003 0xd83ffff6dfad5000 0xffffe01c07000003 0xf03ffffffd9c0000

def z264 : W := mkw 0xa88bb8d67598442a 0xaf3df42c2fbdd855 0xff8fe0fc7f1dfc7f 0xffecd27e3d9ccc7f

def z265 : W := mkw 0x041403208824a094 0x0000000100422322 0x00001f0380e20380 0x0000000002633380

def z266 : W := mkw 0x0000022000008001 0x4002014000400120 0x00001fe3f8ffe3f3 0xcf133dc00263f3e0

def z267 : W := mkw 0x1000000000000001 0x4002094090000000 0x7c7c000000000000 0x700001c1f8000000

def z268 : W := mkw 0x0d2065001a416900 0x0080000900120e83 0x000000000001ff8c 0x0180000000000f87

def z269 : W := mkw 0x0001885264900000 0x8008f400010d5000 0x0003e0fc7ffe0003 0x8e2cfc00059ff000

def z270 : W := mkw 0x0000462900019243 0x483203d0064005a8 0x8003ff000001fff2 0x497003f006000ff8

def z271 : W := mkw 0x4000000000000000 0x0000028240000000 0x7ff0000000000000 0x6000038fc0000000

def z272 : W := mkw 0x8888a04431084428 0xa70890082118c855 0x0003e0fc7f1dfc7f 0x8fecd000059ccc7f

def z273 : W := mkw 0xa88bb8d67598442a 0x883df42c0fbd5811 0x8383e01c07001c00 0x006cc23e059c0c18

def z274 : W := mkw 0x724256a900019243 0xd83ffff6dee005a8 0xfffc1f0380000383 0xf03ffffffa600380

def z275 : W := mkw 0xa889a8447108442a 0xaf38f02c2f1dc855 0xff8ffffc7ffdfc7f 0xfffcf27e3f9fcc7f

def z276 : W := mkw 0x5240000000000001 0x50020bd2d0000000 0x0070000000000000 0x00000181c0000000

def z277 : W := mkw 0xffe9ed447b496d2b 0xffbfffffff1fced7 0xfffffffc7ffdffff 0xffffffffff9fcfff

def z278 : W := mkw 0x0000440000010000 0x0000028000000480 0x000000000001ff80 0x4100038000000f80

def z279 : W := mkw 0x0800200010004000 0x0000000800100801 0x0003e0007f01fc0c 0x0b800000041c0c07

def z280 : W := mkw 0x000290d224900000 0x800d940001a85000 0x00001ffff8fe0003 0x8e1f3c0003e3f000

def z281 : W := mkw 0x49216c0052414902 0x08b0628a46150c81 0x7ff3e00007001c02 0xe030e38fc41c0c00

def z282 : W := mkw 0x0000000000000002 0x0830000006000000 0x0003ff0000000002 0x0830000006000000

def z283 : W := mkw 0x0003defb64919242 0x883df40007ed55a8 0x0003fffffffffff3 0x8f7ffc0007fffff8

def z284 : W := mkw 0x101692f2a4b48095 0xe70f9d40b1e8f164 0x000c00ff801e0071 0x140f1c4039e0f060

def z285 : W := mkw 0x5d352b20da64e995 0x6782694bf057ab67 0x7ffc1fe3ffffe3ff 0xff93fdcffa7ff3e7

def z286 : W := mkw 0x45214d004a412902 0x08b0628346070682 0x0073ff0000e1ff82 0x49302381c6030f80

def z287 : W := mkw 0x5240000000000003 0x50376fd2d0000000 0x7ff0000000000002 0xe033ef8fc0000000

def z288 : W := mkw 0x1414010088242094 0x0000080190022202 0x0070000000e20000 0x00002c01c0033000

def z289 : W := mkw 0x888af6ed3109d668 0x2f00000827f8cdfd 0x0003ffffff1dfffc 0x0fc0000007fccfff

def z290 : W := mkw 0x7b616c0052414903 0xd8bffffede150c81 0xffffe00007001c03 0xf03ffffffc1c0c00

def z291 : W := mkw 0xeda9ed447b496d2a 0x88b8f2af4f1f4e93 0xfff3ff1c7fe1ff8e 0xebfce3bfc79f0f9f

def z292 : W := mkw 0x7241885264900003 0xd03ffff6d90d5000 0xfffc00007ffe0003 0xf23ffffff81ff000

def z293 : W := mkw 0x7241885264900000 0x9008fc26d90d5000 0x7ffc00007ffe0000 0xb200fc0ff81ff000

def z294 : W := mkw 0xf2c880442108042b 0xf73ffff6f908c054 0xfffc00fc001c0073 0xf47ffffff980c078

def z295 : W := mkw 0xfac8a04431084429 0xf70a9bfef918c855 0xffffe0fc7f1dfc7f 0xffecd3fffd9ccc7f

def z296 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0x838c000000000001 0x102fde7e38000000

def z297 : W := mkw 0x4240000000000002 0x1035669240000000 0x0000000000000000 0x0000000000000000

def z298 : W := mkw 0x3000000000000001 0xc00a996498000000 0xfffc000000000003 0xf03ffffff8000000

def z299 : W := mkw 0x4800200010004002 0x0030628a40100801 0x7ff3e0007f01fc0e 0xebb0e38fc41c0c07

def z300 : W := mkw 0x0000000000000000 0x2700000020008044 0x7c0c0000781c000c 0xb28010003800c007

def z301 : W := mkw 0x452045000a412900 0x0080028340020682 0x0070000000000380 0x00000181c0000380

def z302 : W := mkw 0x0801280050004002 0x0830600806150801 0x7f83ff007fe1fc0e 0xebb0e20e061f0c07

def z303 : W := mkw 0x1000000000000001 0x67020940b0008044 0x7c7c00e0781de07f 0xff933dc1f800c067

def z304 : W := mkw 0x000398d264900000 0x8808900007ad5000 0x0003fffffffe0003 0x8e2cd00007fff000

def z305 : W := mkw 0x0000022000008001 0x4002014000400120 0x000000000001e3f0 0x410001c0000003e0

def z306 : W := mkw 0xbc9ca144b92c64bc 0xa708982db91aea57 0xffffe0fc7ffffc7f 0xffecfe7ffd9ffc7f

def z307 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0x7f8fe0007f1dfc0e 0xfba0d20e3c1ccc07

def z308 : W := mkw 0x524256a900019243 0x58376fd2d6e005a8 0x00701f0380000380 0x00132d81c2600380

def z309 : W := mkw 0x0003189244900002 0x0835640006a51000 0x0000000000000000 0x0000000000000000

def z310 : W := mkw 0xb09c8264a12c84bd 0xe70a9964b948e174 0x800c00ff801e0071 0x144f1c7039e0f078

def z311 : W := mkw 0x6000000000000002 0x8038f2a648000000 0xfffc000000000003 0xf03cf3fff8000000

def z312 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x80001fff800003f1 0x045f01f003e003f8

def z313 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x80001f0380000383 0x403f03f002600380

def z314 : W := mkw 0x0000440000010002 0x0830028006000480 0x0003e00000001c00 0x0020020004000c00

def z315 : W := mkw 0x3240000000000003 0xd03ffd7498000000 0x800c000000000003 0x903ffc7038000000

def z316 : W := mkw 0x000256a900019242 0x0830028006e005a8 0x0003ffff8001fff2 0x4d70038007e00ff8

def z317 : W := mkw 0x000256a900019240 0x0800000006e005a8 0x8003ffff8001fff3 0x4d6c027007e00ff8

def z318 : W := mkw 0x5240000000000003 0x50376fd2d0000000 0x0070000000000000 0x00132d81c0000000

def z319 : W := mkw 0x7240000000000001 0xd00afff6d8000000 0xfffc000000000000 0xf000fffff8000000

def z320 : W := mkw 0x141657a98825b2d5 0x6f020941b6e2a7ee 0x7c7ffffff8ffffff 0xffd33dc1ffe3ffff

def z321 : W := mkw 0x0800a04030004000 0x8008900801184801 0x7f83e0fc7f1dfc0f 0xefacd20e059ccc07

def z322 : W := mkw 0x000212a900009243 0x403703d000e00128 0x800000ff80000073 0x447f03f001e00078

def z323 : W := mkw 0x0400450008012002 0x0830028106020682 0x7c73ff0078e1ff8e 0xebb02381c6030f87

def z324 : W := mkw 0x7240000000000000 0x9008fc26d8000000 0xfffc000000000003 0xf02cfe7ff8000000

def z325 : W := mkw 0x0003defb64919243 0xc83ff7d007ed55a8 0x8003ffff8701fff3 0x4d7fc3f007fc0ff8

def z326 : W := mkw 0x141403208824a095 0x4002094190422322 0x7c701f03f8e3e38e 0xeb932d81c2633387

def z327 : W := mkw 0x1014000080240094 0x27000800b000a044 0x000c0000001e0000 0x10001c003800f000

def z328 : W := mkw 0x7240462900019241 0x50020bf6d84005a8 0xfffc00000001fff0 0x714003fff8000ff8

def z329 : W := mkw 0x765403208824a095 0x77020bf7f842a366 0xfffc1fe3f8ffe3ff 0xff933ffffa63f3e7

def z330 : W := mkw 0x0d2129005a406900 0x0080000900170a03 0x000000007fe0000c 0x02800000001f0007

def z331 : W := mkw 0x5d3467209a65e995 0x67820bcbf052afe7 0x7ffc1fe3f8ffffff 0xff933fcffa63ffe7

def z332 : W := mkw 0x2000804020000000 0x8008902409084000 0xff8fe0fc7f1c0003 0xfe2cd27e3d9cc000

def z333 : W := mkw 0xfacbb8d67598442b 0xff3ffffeffbdd855 0xfffffffffffffc7f 0xfffffffffffffc7f

def z334 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c1fe38001e3ff 0x7d9301c1fa6003e7

def z335 : W := mkw 0x4d2129005a406900 0x0080600b40170a03 0x7ff01f007fe1e38e 0xeb90e18fc21f0387

def z336 : W := mkw 0x141403208824a095 0x67020941b042a366 0xfc7ffffff8ffffff 0xffff3ff1ffe3ffff

def z337 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001fe3f8fe0000 0x0e0000000263f000

def z338 : W := mkw 0x6240000000000002 0x903df6b648000000 0xfff0000000000002 0xe03ce3bfc0000000

def z339 : W := mkw 0xe888a0443108442a 0xa738f2ae6918c855 0xffffe0fc7f1dfc7f 0xfffcf3fffd9ccc7f

def z340 : W := mkw 0x0002108000000002 0x0835000006a00000 0x0003fffff8fe0003 0x8e3f3c0007e3f000

def z341 : W := mkw 0x7240000000000002 0x9038fea6d8000000 0x7ffc000000000002 0xf030ff8ff8000000

def z342 : W := mkw 0x49216c0052414902 0x08b0628a46150c81 0x0383ff000701ff82 0x4930c38e061c0f80

def z343 : W := mkw 0x14150b20c824a097 0x6f326941b647a366 0x7c7fffe3ffffe3ff 0xffb3fdc1fe7ff3e7

def z344 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c00e3f8fe007d 0xb6833c41f863f067

def z345 : W := mkw 0x0000804020000000 0xa70890002108c044 0x7c0fe0fc7f1de07f 0xffacd0403d9cc067

def z346 : W := mkw 0x200398d264900002 0x883df4240fad5000 0xff8ffffffffe0003 0xfe3ffe7e3ffff000

def z347 : W := mkw 0x141403208824a095 0x4002094190422322 0x7c7c1f0380e20383 0xf0133dc1fa633380

def z348 : W := mkw 0x765403208824a095 0xf70afd67f842a366 0x7ffc1fe3f8ffe3ff 0xff93fdcffa63f3e7

def z349 : W := mkw 0x040257a90801b243 0x483703d106e207aa 0xfc73fffff8e1ffff 0xefff23f1c7e30fff

def z350 : W := mkw 0x4923fcd276d14902 0x88bdf68a47bd5c81 0x0383fffffffe1c03 0x8e3ffe0e07fffc00

def z351 : W := mkw 0x0001884060000002 0x8838f000070d4000 0x0003fffc7ffc0003 0x8e3cf000079fc000

def z352 : W := mkw 0x101612a9802492d5 0x67070950b0e0a16c 0x800c00ff801e0071 0x144f1c7039e0f078

def z353 : W := mkw 0x5d352900da646994 0x2780680bf017aa47 0x7ffc00007ffe000c 0xb280fc0ff81ff007

def z354 : W := mkw 0x4d237fa95a41fb42 0x08b0628b46f70fab 0x7ff3ffffffe1fffe 0xeff0e38fc7ff0fff

def z355 : W := mkw 0x14158952ecb42094 0xa708fc01b10ff246 0x7c7c00007ffe000c 0xb280fc01f81ff007

def z356 : W := mkw 0x7243189244900003 0xd83ffff6dea51000 0xfffc1f0380e20003 0xf03ffffffa633000

def z357 : W := mkw 0x1000000000000001 0x4002094090000000 0x0070000000000000 0x00132d81c0000000

def z358 : W := mkw 0x14179bf2ecb4a097 0xc83ffd4197ef7322 0x0073fffffffe0383 0x8e3ffd81c7fff380

def z359 : W := mkw 0x724398d264900002 0x983dfc26dfad5000 0x7ffffffffffe0003 0xbe3ffc0ffffff000

def z360 : W := mkw 0x0002108000000003 0x483703d006a00000 0x8003ffff80000003 0x4c3f03f007e00000

def z361 : W := mkw 0x5f616d005a416903 0x58b76fdbd6170e83 0x7ff3ff007fe1ff8e 0xebb3ef8fc61f0f87

def z362 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001f0380e20000 0x00132c0002633000

def z363 : W := mkw 0x0414010088242094 0x270000012002a246 0x0000000078fe000c 0x028000000003f007

def z364 : W := mkw 0x7f6129005a406903 0xd0bfffffd8170a03 0xfffc00007fe0000f 0xf2bffffff81f0007

def z365 : W := mkw 0x7240000000000001 0x50020bf6d8000000 0xfffc000000000003 0xf0133ffff8000000

def z366 : W := mkw 0x7241080040000003 0xd83ffff6de050000 0xffffff007fe00003 0xfa3ffffffe1f0000

def z367 : W := mkw 0x0000022000008001 0x4002014000400120 0x8003ffff8001fff3 0x4d7f03f007e00ff8

def z368 : W := mkw 0x0000000000000000 0x0000000000000000 0x800000fc00000071 0x044c007001800078

def z369 : W := mkw 0x0000000000000000 0x0000000000000000 0x8000000000000003 0x402c027000000000

def z370 : W := mkw 0x0002108000000002 0x0835000006a00000 0x0003e01c00000000 0x002c000005800000

def z371 : W := mkw 0x1000000000000001 0x4002094090000000 0x000c000000000001 0x10031c4038000000

def z372 : W := mkw 0x8c9ca364b92ce4bc 0x27000009215aeb77 0x0003fffffffffffc 0x0fc0000007ffffff

def z373 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0x83f0000000000000 0x003fefbfc0000000

def z374 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8c00fc7f1c007d 0xb6ccd07e399cc07f

def z375 : W := mkw 0xbc9ca144b92c64bc 0xa708982db91aea57 0x7ffc00007ffe000c 0xb280fc0ff81ff007

def z376 : W := mkw 0x0000000000000001 0x4002014000000000 0x0000000000000003 0x401301c000000000

def z377 : W := mkw 0x0000804020000000 0x8008900001084000 0x000000fc001c0001 0x040c10000180c000

def z378 : W := mkw 0x541403208824a097 0x67326bc3f042a366 0x7ffc1fe3f8ffe3ff 0xffb3ffcffa63f3e7

def z379 : W := mkw 0x6b616c0052414902 0x98bdf6be4e150c81 0x8383e00007001c00 0x002cc23e041c0c00

def z380 : W := mkw 0x0003189244900002 0x883df40006a51000 0x00001f0380e20003 0x803ffc0002633000

def z381 : W := mkw 0x7240804020000003 0xd03ffff6d9084000 0xffffe0fc7f1c0003 0xfe3ffffffd9cc000

def z382 : W := mkw 0x141403208824a094 0x27000801b042a366 0x7c7c1fe3f8ffe3fc 0xbf803c01fa63f3e7

def z383 : W := mkw 0x000256a900019242 0x0835029006e005a8 0x8003ffff8001fff0 0x0d6c023007e00ff8

def z384 : W := mkw 0x0d237fa95a41fb40 0x0880000906f70fab 0x0003ffffffe1fffc 0x0fc0000007ff0fff

def z385 : W := mkw 0x0800200010004000 0x0000000800100801 0xff83e0fc7f01fc7f 0xefecc27e059c0c7f

def z386 : W := mkw 0xa088804421080428 0xa70890242908c054 0x000c0000001c0000 0x100010003800c000

def z387 : W := mkw 0xeda9ed447b496d2a 0xafb8f2af6f1fced7 0x7fffff007ffdff8e 0xfbb0f38ffe1fcf87

def z388 : W := mkw 0x6f616d005a416902 0x98bdf6bf4e170e83 0xfff3ff007fe1ff8e 0xebbce3bfc61f0f87

def z389 : W := mkw 0x3240000000000001 0xd00f9d7498000000 0xff8c000000000003 0xf02fde7e38000000

def z390 : W := mkw 0x0000462900019240 0x00000000004005a8 0x000000000001fff0 0x0140000000000ff8

def z391 : W := mkw 0x0000462900019241 0x400203d0004005a8 0x80001fe38001fff3 0x4d5303f002600ff8

def z392 : W := mkw 0x2000000000000000 0x8008902408000000 0x7f8c000000000000 0xb000d00e38000000

def z393 : W := mkw 0x0000000000000002 0x0030600000000000 0x0000000000000002 0x8030e00000000000

def z394 : W := mkw 0x4d2065001a416900 0x0080028b40120e83 0x7ff3e0007f01ff8e 0xeba0c38fc41c0f87

def z395 : W := mkw 0x09216c0052414900 0x0880000806150c81 0x0003e00007001c00 0x00000000041c0c00

def z396 : W := mkw 0xe9a9ec4473494d2a 0x88b8f2ae4f1d4c91 0x8383e01c07001c00 0x006cc23e059c0c18

def z397 : W := mkw 0x5d356f20da65e997 0x6fb26bcbf657afe7 0x7fffff007fe1fffe 0xfbb0e3cffe1f0fe7

def z398 : W := mkw 0xa888200411084428 0x2700002c28108855 0xff8fe0007f01fc7e 0xfbe0c27e3c1c0c7f

def z399 : W := mkw 0xa888a04431084428 0x2700002c2918c855 0xff8fe0fc7f1dfc7c 0x7fc0027e3d9ccc7f

def z400 : W := mkw 0x1000000000000001 0x4002094090000000 0x7c7c1fe3f8fe0003 0xfe133dc1fa63f000

def z401 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c1f0380e3e3fc 0x71932dc1fa6333e7

def z402 : W := mkw 0xb888a04431084429 0xe70a996cb918c855 0xffffe0fc7f1dfc7f 0xfffffffffd9ccc7f

def z403 : W := mkw 0x0400010008002000 0x2700000120028246 0x7c7c1fe078fde3ff 0xff9031c1fa03c3e7

def z404 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x0003ff038001ff82 0x4933038006600f80

def z405 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x0003ffff8001fff0 0x0d53018007e00ff8

def z406 : W := mkw 0x888bb8d67598442a 0xaf3df40827bdd855 0x0003fffffffffc7f 0x8ffffc0007fffc7f

def z407 : W := mkw 0x0000000000000003 0xc03ff7d000000000 0x8000000000000003 0xc03ffff000000000

def z408 : W := mkw 0x3240000000000003 0xd03f9ff498000000 0x800c000000000003 0x503f1ff038000000

def z409 : W := mkw 0x4000440000010002 0x0830628246000480 0x7ff3ff000001ff82 0xe930e38fc6000f80

def z410 : W := mkw 0xbc9fbbf6fdbce4bf 0xef3ffd6dbffffb77 0xffffffffffffffff 0xffffffffffffffff

def z411 : W := mkw 0x000398d264900000 0x880d940007ad5000 0x0003fffffffe0001 0x0e0f1c0007fff000

def z412 : W := mkw 0xa888a04431084428 0x8008902c09184811 0xff83e01c7f01fc0e 0xebecc23e059c0c1f

def z413 : W := mkw 0x0003189244900000 0x0800000006a51000 0x00001f0380e20000 0x0000000002633000

def z414 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c1f03f8fe038c 0xb2933d81fa63f387

def z415 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xffffe0fc0001fc73 0xfd7ffffffd800c78

def z416 : W := mkw 0xfac8a0443108442b 0xf73ffffef918c855 0xfffc00007f1c000f 0xf2bffffff81cc007

def z417 : W := mkw 0x7254022080248097 0xf73ffff6f840a164 0xfffc00e3801e0073 0xf43ffffff860f060

def z418 : W := mkw 0xa088804421080428 0xa70890242908c054 0xfc0c00fc781de07f 0xffcc10703980c07f

def z419 : W := mkw 0x7240000000000003 0x50370bf6d8000000 0xfffc000000000003 0x703f03fff8000000

def z420 : W := mkw 0xa88af4cd3109566a 0xaf3d92bc2fb8ccdd 0xff8fe0fc7f1dfc7f 0xffecd27e3d9ccc7f

def z421 : W := mkw 0xeda9a9447b486d28 0xa788f02f691fca57 0xffffe0fc7ffdfc7f 0xffecf27ffd9fcc7f

def z422 : W := mkw 0x5000000000000003 0x40326bc2d0000000 0x7ffc000000000003 0xf033ffcff8000000

def z423 : W := mkw 0x8da9ed447b496d28 0x2f800009271fced7 0x0003fffc7ffdfffc 0x0fc00000079fcfff

def z424 : W := mkw 0x0003189244900002 0x0835640006a51000 0x0003ff03ffe20002 0x8a33ec00067f3000

def z425 : W := mkw 0x4d23fdd27ed16902 0x88bdf68b47bf5e83 0x7ff3ff1c7fe1ff8e 0xebbce38fc79f0f87

def z426 : W := mkw 0xb89ca264b12cc4bd 0xe70a996cb958e975 0xff8fe0ffff1ffc7f 0xffefde7e3dfcfc7f

def z427 : W := mkw 0x0d216d005a416902 0x08b0028906170e83 0x0003ff007fe1ff8e 0x4bb00380061f0f87

def z428 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x00001f03fffe0000 0x8213fc00027ff000

def z429 : W := mkw 0xa88af4cd3109566a 0x883d92bc0fb84c99 0x8383e01c07001c00 0x006cc23e059c0c18

def z430 : W := mkw 0x0400010008002000 0x0000000100020202 0x7c7000000001e38c 0x61800181c0000387

def z431 : W := mkw 0x7f6129005a406900 0x9088fc2fd8170a03 0x7ffc00007fe0000c 0xb280fc0ff81f0007

def z432 : W := mkw 0xfac8a04431084428 0xb708fc2ef918c855 0x7ffc00007f1c000c 0xb280fc0ff81cc007

def z433 : W := mkw 0x1414010088242095 0x67020941b002a246 0x7c7c000078fe000f 0xf2933dc1f803f007

def z434 : W := mkw 0x7240440000010003 0xd83ffff6de000480 0xffffff000001ff83 0xf93ffffffe000f80

def z435 : W := mkw 0x0000804020000002 0x803df40001084000 0x0003e0fc7f1c0003 0x8e3ffc00059cc000

def z436 : W := mkw 0xa888200411084428 0x2700002c28108855 0x7f8c00000000000c 0x3080000e38000007

def z437 : W := mkw 0xeda865041b496d28 0x278002af68128ed7 0xfffc00000001fffc 0x71c003fff8000fff

def z438 : W := mkw 0x7f637fa95a41fb43 0xd8bfffffdef70fab 0xffffffffffe1ffff 0xffffffffffff0fff

def z439 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8ffffffffffc7f 0xfffffe7e3ffffc7f

def z440 : W := mkw 0x5d356f20da65e997 0x48b26bcbd6572fa3 0x7ff3ff03ffe3ff8e 0xebb3ef8fc67f3f87

def z441 : W := mkw 0x080276a91001d243 0x483703d806f00da9 0xff83ffffff01ffff 0xefffc3fe07fc0fff

def z442 : W := mkw 0x7a40200010004003 0xd03ffffed8100801 0xffffe0007f01fc0f 0xfbbffffffc1c0c07

def z443 : W := mkw 0x0000440000010000 0x0800000006000480 0x0003ff000001ff80 0x0900000006000f80

def z444 : W := mkw 0x0400010008002000 0x0000000100020202 0x00001f0078e1e38c 0x0b80000002030387

def z445 : W := mkw 0x0002108000000000 0x0800000006a00000 0x0003ffff80000000 0x0c00000007e00000

def z446 : W := mkw 0x000212a900009241 0x4007015000e00128 0x80001fff8001e3f3 0x4d5f01f003e003f8

def z447 : W := mkw 0x7240000000000002 0x903dfeb6d8000000 0xfffc000000000000 0xb02cfe3ff8000000

def z448 : W := mkw 0x0000000000000000 0x0000000000000000 0x0003e0fc0001fc70 0x0d40000005800c78

def z449 : W := mkw 0x0400010008002000 0x0000000100020202 0x00701f0000e00380 0x00102181c2030380

def z450 : W := mkw 0x4d216f205a41e903 0x48b263cb46570fa3 0x7ff3ffe3ffe1ffff 0xefb3e3cfc67f0fe7

def z451 : W := mkw 0x8888a04431084428 0x270000082118c855 0x7f83e0fc7f1dfc7e 0xefe0c20e059ccc7f

def z452 : W := mkw 0x4d2065001a416902 0x08b0028b46120e83 0x7ff3ff000001ff8e 0x69b0038fc6000f87

def z453 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0x838fe0fc071c1c71 0x146cd27e3d9ccc78

def z454 : W := mkw 0x0002548900011242 0x0835029006a00488 0x8003ffff80001c03 0x0c7f023007e00c18

def z455 : W := mkw 0x6240000000000002 0x903df6b648000000 0x8380000000000003 0x803ffe3e00000000

def z456 : W := mkw 0x100398d264900003 0xc83ffd4097ad5000 0x7c7ffffffffe0003 0xfe3ffdc1fffff000

def z457 : W := mkw 0x0d23fdd27ed16902 0x88bdf40907bf5e83 0x0003ffffffffff8f 0x8fbffc0007ffff87

def z458 : W := mkw 0x000398d264900002 0x0835640007ad5000 0x0003fffffffe0000 0x0e132c0007fff000

def z459 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000003 0x80133c0000000000

def z460 : W := mkw 0x0000804020000000 0x8008900001084000 0x8003e0fc7f1dfc73 0xcf6cd270059ccc78

def z461 : W := mkw 0xa888200411084428 0x0000002c08100811 0x8380000000001c00 0x0040023e00000c18

def z462 : W := mkw 0x400256a900019243 0x483763d246e005a8 0xfff3ffff8001fff3 0xed7fe3ffc7e00ff8

def z463 : W := mkw 0x77614d004a412903 0xd8bffff7de070682 0xfffc1f0000e00383 0xf03ffffffa030380

def z464 : W := mkw 0x7240000000000002 0x903dfc26d8000000 0x7ffc000000000003 0xb03ffc0ff8000000

def z465 : W := mkw 0x0000804020000000 0x8008900001084000 0x000000007f1c0000 0x8200d000001cc000

def z466 : W := mkw 0x1414010088242094 0x27000801b002a246 0x7c7c1f0078ffe38e 0xfb903d81fa03f387

def z467 : W := mkw 0xa888e4443109442a 0xaf3892ac2f18ccd5 0xff8ffffc7f1dffff 0xfffcd3fe3f9ccfff

def z468 : W := mkw 0xfacaf6ed3109d66b 0xff3ffffefff8cdfd 0xffffffffff1dffff 0xfffffffffffccfff

def z469 : W := mkw 0x4d216d005a416903 0x48b763db46170e83 0xfff3ff007fe1ff8f 0xebbfe3ffc61f0f87

def z470 : W := mkw 0x141657a98825b2d7 0x6f370bd1b6e2a7ee 0x7c7c1fe3f8ffe3ff 0xff933dc1fa63f3e7

def z471 : W := mkw 0x4d216d005a416902 0x88bdf68b46170e83 0x7ff3ff007fe1ff8f 0xebbfff8fc61f0f87

def z472 : W := mkw 0x5240000000000000 0x10006c02d0000000 0x0070000000000000 0x00002c01c0000000

def z473 : W := mkw 0xb2c8804421080429 0xf70f9d74b908c054 0x800c00fc001c0071 0x144f1c703980c078

def z474 : W := mkw 0x0000462900019243 0x403703d0004005a8 0x800000000001fff3 0x417f03f000000ff8

def z475 : W := mkw 0x141403208824a097 0x67370bd1b042a366 0xfc7c1fe3f8ffe3ff 0xffbf3ff1fa63f3e7

def z476 : W := mkw 0x45235d924ed12902 0x08b5668346a71682 0x00701f0380e20380 0x00132d81c2633380

def z477 : W := mkw 0xa088000401080428 0x2700002428008054 0x800c000000000070 0x1040007038000078

def z478 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0x7f8fe0fc7f1dfc7c 0xbfc0d00e3d9ccc7f

def z479 : W := mkw 0x57614d004a412903 0x58b76fd3d6070682 0x00701f0000e00380 0x00132d81c2030380

def z480 : W := mkw 0x324212a900009241 0xd00f9d7498e00128 0x800c00ff80000071 0x144f1c7039e00078

def z481 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0x7ffc000000000000 0xb013fd8ff8000000

def z482 : W := mkw 0xa088804421080428 0x8008902409084010 0x8000001c00000000 0x004c003001800018

def z483 : W := mkw 0x0000000000000002 0x0035000000000000 0x0000000000000003 0x003f000000000000

def z484 : W := mkw 0x1000000000000000 0x0000080090000000 0x7c7c000000000000 0xb0003c01f8000000

def z485 : W := mkw 0xa088804421080428 0xa70890242908c054 0x800fe0fc001dfc73 0x5d6c12703d80cc78

def z486 : W := mkw 0x141403208824a095 0x4002094190422322 0x00701fe380e3e3f3 0x4d132dc1c26333e0

def z487 : W := mkw 0xcda9ed447b496d2a 0x2fb0628b671fced7 0x7ff3fffc7ffdfffe 0xeff0e38fc79fcfff

def z488 : W := mkw 0x1417dffbecb5b2d7 0xef3fffd1b7eff7ee 0xfc7fffffffffffff 0xfffffff1ffffffff

def z489 : W := mkw 0x4d2129005a406902 0x00b0628b40170a03 0x7ff000007fe0000e 0xe2b0e38fc01f0007

def z490 : W := mkw 0x00039af264908003 0xc83ff54007ed5120 0x0003ffffffffe3f3 0xcf3ffdc007fff3e0

def z491 : W := mkw 0x0000440900011240 0x0000029000000488 0x8000000000001c00 0x0040023000000c18

def z492 : W := mkw 0x0000022000008000 0x0000000000400120 0x00001fe38001e3f0 0x0d000000026003e0

def z493 : W := mkw 0x7654010088242097 0xf73ffff7f802a246 0xfffc000078fe000f 0xf2bffffff803f007

def z494 : W := mkw 0x0d216d005a416902 0x08b0600906170e83 0x0003ff007fe1ff8e 0x8bb0e000061f0f87

def z495 : W := mkw 0x14171bb2ccb4a097 0x6f376d41b6e7b366 0x7c7c1fe3f8ffe3ff 0xff933dc1fa63f3e7

def z496 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3e0007fe01c0c 0xa2a0e20fc41f0c07

def z497 : W := mkw 0x1400010008002001 0x4002094190020202 0x7c7c1f0078e1e38f 0xfb933dc1fa030387

def z498 : W := mkw 0xa889a85675984428 0xa708f42c291dd855 0xff8fe0fc7ffffc7f 0xffecfe7e3d9ffc7f

def z499 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8fe01c0701fc7c 0x71ecc27e3d9c0c7f

def z500 : W := mkw 0x624398d264900002 0x983df6b64fad5000 0x8383e01c07000000 0x002cc23e059c0000

def z501 : W := mkw 0x400398d264900002 0x883df68247ad5000 0x7ff3fffffffe0003 0xee3fff8fc7fff000

def z502 : W := mkw 0x000290d224900000 0x800d940001a85000 0x0003e0ffff1e0003 0x8e2fdc0005fcf000

def z503 : W := mkw 0x55354f20ca65a997 0x6fb26bc3f647a7e6 0x7c7c1fe3f8ffe3ff 0xff933dc1fa63f3e7

def z504 : W := mkw 0x0001885264900002 0x8838f400070d5000 0x0003ff007ffe0002 0x8a30fc00061ff000

def z505 : W := mkw 0x1014022080248095 0x67020940b040a164 0x000c1fe3801fe3f3 0x5d131dc03a60f3e0

def z506 : W := mkw 0x341403208824a095 0xe70a9965b842a366 0xfffc1fe3f8ffe3ff 0xffbffffffa63f3e7

def z507 : W := mkw 0x0000022900009241 0x4002015000400128 0x8000000000000070 0x0040007000000078

def z508 : W := mkw 0x4d23fdd27ed16902 0x08b0628b47bf5e83 0x7ff3ffffffffff8e 0xefb0e38fc7ffff87

def z509 : W := mkw 0xfdbdef64fb6dedbf 0xefbafbefff5feff7 0xffffffffffffffff 0xffffffffffffffff

def z510 : W := mkw 0x5240000000000003 0x50376fd2d0000000 0x7c7c000000000003 0xf0133dc1f8000000

def z511 : W := mkw 0xa88ab0d635984428 0xa70d942c29b8d855 0xff8fe0ffff1ffc7f 0xffefde7e3dfcfc7f

def z512 : W := mkw 0x5d216d005a416903 0x48b26bcbd6170e83 0x7fffff007fe1ff8f 0xfbb3ffcffe1f0f87

def z513 : W := mkw 0xa08ad6ed2109966b 0xef3f93f42fe8c5fc 0x800fffff801dfff3 0x5d7f13f03fe0cff8

def z514 : W := mkw 0x5d356d00da656996 0x2fb06a8bf617aec7 0x7fffff007fffff8e 0xfbb0ff8ffe1fff87

def z515 : W := mkw 0x4d21ed407a416902 0x88b8f28b471f4e83 0x7ff3fffc7ffdff8f 0xefbcf38fc79fcf87

def z516 : W := mkw 0x2000000000000000 0x8008902408000000 0xff8fe0fc0001fc73 0xfd6cd27e3d800c78

def z517 : W := mkw 0x2000000000000000 0xa708902428008044 0xff8c00e0781de07f 0xffacd27e3800c067

def z518 : W := mkw 0x00035ea940019243 0x483763d006e505a8 0x8003ffffffe1fff3 0xcf7fe3f007ff0ff8

def z519 : W := mkw 0x4923fcd276d14902 0x88bdf68a47bd5c81 0x0383e01c07001c00 0x002cc20e059c0c00

def z520 : W := mkw 0x8088804421080428 0x270000002108c054 0x000000fc001c0070 0x044000000180c078

def z521 : W := mkw 0x49216c0052414902 0x08b0628a46150c81 0x0383ff007fe01c02 0x8a30e20e061f0c00

def z522 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8c00007f1dfc7c 0xf3c0d27e381ccc7f

def z523 : W := mkw 0x5d377fa9da65fbd7 0x6fb76bdbf6f7afef 0xffffffffffffffff 0xffffffffffffffff

def z524 : W := mkw 0x4d216d005a416902 0x2fb0628b66178ec7 0x7fffffe07ffdffff 0xffb0f3cffe1fcfe7

def z525 : W := mkw 0x000398d264900002 0x0830600007ad5000 0x0003fffffffe0002 0x8e30e00007fff000

def z526 : W := mkw 0xbc9ef7edb92df6ff 0xef3f9bfdbffaefff 0xffffffffffffffff 0xffffffffffffffff

def z527 : W := mkw 0xbc9ca364b92ce4bd 0xe70a996db95aeb77 0xffffe0fc7f1dffff 0xffecd3fffd9ccfff

def z528 : W := mkw 0x0d216d005a416900 0x0880000906170e83 0x7c73ff007fe1ff8e 0xeb902181c61f0f87

def z529 : W := mkw 0x0400010008002000 0x0000000100020202 0x7c701fe3f8ffe38f 0xef933d81c263f387

def z530 : W := mkw 0x0000805224900000 0x8008940001085000 0x00000000001e0000 0x00001c000000f000

def z531 : W := mkw 0x0002108900001240 0x0005001000a00008 0x8000001c00000000 0x004c003001800018

def z532 : W := mkw 0x000256a900019240 0x0800000006e005a8 0x00001f0380000380 0x0000000002600380

def z533 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001f0078e00002 0x8a10200002030000

def z534 : W := mkw 0xa888200411084428 0x2700002c28108855 0xff8c00e0781dfc7f 0xffc0127e3800cc7f

def z535 : W := mkw 0x0001080040000000 0x0800000006050000 0x0003ff007fe00000 0x0a000000061f0000

def z536 : W := mkw 0x0800200010004000 0x0000000800100801 0x7f8000000001fc0c 0x6180020e00000c07

def z537 : W := mkw 0x000290d224900002 0x803df40001a85000 0x000000ff801e0003 0x843ffc0001e0f000

def z538 : W := mkw 0xa88ab2ed3108d669 0xe70f917c29f8c97d 0xff8fe0ffff1dfc7f 0xffefd27e3dfccc7f

def z539 : W := mkw 0x49237c8952415b42 0x08b5629a46b50c89 0x8383e01c07001c00 0x006cc23e059c0c18

def z540 : W := mkw 0x3240000000000000 0x90089c2498000000 0x000c000000000000 0x10001c0038000000

def z541 : W := mkw 0x000212a900009240 0x0000000000e00128 0x000000ff80000070 0x0440000001e00078

def z542 : W := mkw 0x0003defb64919243 0xc83ff7d007ed55a8 0x0003fffffffe0383 0x8e3ffd8007fff380

def z543 : W := mkw 0x4d2277a91a41fb43 0x48b703db46f20fab 0xfff3ffff8001ffff 0x6dff03ffc7e00fff

def z544 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x0383ff007fe1ff8c 0x0ba0c20e061f0f87

def z545 : W := mkw 0x000256a900019241 0x4802014006e005a8 0x0003ffff8001fff3 0x4d5301c007e00ff8

def z546 : W := mkw 0x76579bf2ecb4a097 0xff3ffff7ffeff366 0xffffffffffffe3ff 0xffbffffffffff3e7

def z547 : W := mkw 0x6d216d005a416902 0x88b8f2af4e170e83 0xffffff007fe1ff8f 0xfbbcf3fffe1f0f87

def z548 : W := mkw 0x0000000000000001 0x400203d000000000 0x8000000000000000 0x400003f000000000

def z549 : W := mkw 0x0d216d005a416900 0x0880000906170e83 0x7f83ff007fe1ff8e 0xeba0c20e061f0f87

def z550 : W := mkw 0x7f63fdd27ed16903 0xd8bfffffdfbf5e83 0xffffffffffffff8f 0xffbfffffffffff87

def z551 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001fe380000003 0x0c13000002600000

def z552 : W := mkw 0x0000000000000000 0x8008900000000000 0x0000000000000003 0x802cd00000000000

def z553 : W := mkw 0x55354f20ca65a997 0x48b26bc3d64727a2 0x00701f0380e20380 0x00132d81c2633380

def z554 : W := mkw 0x0001081244900000 0x0000640000051000 0x0000000000e20000 0x00002c0000033000

def z555 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0x7f8c00e07f1de07f 0xff80d04e381cc067

def z556 : W := mkw 0x000398d264900002 0xaf3df40027add044 0x7c0fffffffffe07f 0xffbffc403ffff067

def z557 : W := mkw 0xeac8a0443108442a 0xb73df6be6918c855 0xff8fe0fc7f1dfc7f 0xffecd27e3d9ccc7f

def z558 : W := mkw 0x0000804020000000 0x0000000001084000 0x0003e0fc7f1c0000 0x0e000000059cc000

def z559 : W := mkw 0x3240000000000001 0xd00f9d7498000000 0xfc7c000000000003 0xf01f3df1f8000000

def z560 : W := mkw 0x00035ebb44919243 0x483767d006e515a8 0x00001f0380e20380 0x00132d8002633380

def z561 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x0073ff007fe1ff8c 0x0b902181c61f0f87

def z562 : W := mkw 0x1000000000000003 0xc03ffd4090000000 0x7c7c000000000003 0xf03ffdc1f8000000

def z563 : W := mkw 0x141657a98825b2d7 0x6f370bd1b6e2a7ee 0xfc7fffff8001ffff 0x7dff03f1ffe00fff

def z564 : W := mkw 0x000256a900019243 0xc83ff7d006e005a8 0x8003ffff8001fff3 0xcd7ffff007e00ff8

def z565 : W := mkw 0x7f756f20da65e997 0xffbffffffe57afe7 0xffffffe3ffffffff 0xffbffffffe7fffe7

def z566 : W := mkw 0x041657a98825b2d4 0x2f00000126e2a7ee 0x0003fffff8fffffc 0x0fc0000007e3ffff

def z567 : W := mkw 0x5d37fff2fef5e997 0xefbfffcbf7ffffe7 0x7fffffffffffffff 0xffbfffcfffffffe7

def z568 : W := mkw 0x2000000000000002 0x803df42408000000 0xff8c000000000003 0xf03ffe7e38000000

def z569 : W := mkw 0x141657a98825b2d7 0x48370bd196e227aa 0x00701f0380e20380 0x00132d81c2633380

def z570 : W := mkw 0x141693f2acb4a095 0xe70f9d41b1eaf366 0x7c7c1ffff8ffe3ff 0xff9f3dc1fbe3f3e7

def z571 : W := mkw 0x0000440000010002 0x0830028006000480 0x00001f0000000380 0x0010018002000380

def z572 : W := mkw 0x0002d6e920019243 0xc83f93d007e845a8 0x8003ffffff1dfff3 0xcf7fd3f007fccff8

def z573 : W := mkw 0x1414010088242094 0x27000801b002a246 0x7c7c00000000000c 0x30800001f8000007

def z574 : W := mkw 0x0000000000000002 0x0030028000000000 0x0000000000000002 0x4030038000000000

def z575 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0x807c000000000001 0x101f3df1f8000000

def z576 : W := mkw 0x565403208824a097 0x77376fd3f042a366 0x7c7c1fe3f8ffe3ff 0xff933dc1fa63f3e7

def z577 : W := mkw 0x4d21ed527ed16902 0x88b8f68b471f5e83 0x7ff3ff007fffff8e 0xebb0ff8fc61fff87

def z578 : W := mkw 0x040399d26c902002 0x883df40107af5202 0x7c73ffffffffe38f 0xefbffd81c7fff387

def z579 : W := mkw 0x2240000000000000 0x900d943408000000 0x8000000000000000 0x000c003000000000

def z580 : W := mkw 0xeda8e5443b496d28 0xa78892af691aced7 0xffffe0fc7f1dffff 0xffecd3fffd9ccfff

def z581 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003ff1c7fe00002 0x8a3ce000079f0000

def z582 : W := mkw 0x8888a04431084428 0x270000082118c855 0x000000007f1c000c 0x02800000001cc007

def z583 : W := mkw 0x0000000000000000 0x2700000020008044 0x7c0c1fe3f8ffe07f 0xff933c403a63f067

def z584 : W := mkw 0x0003188040000002 0x0835600006a50000 0x0003ffffffe00003 0x8e3fe00007ff0000

def z585 : W := mkw 0x101656a9802592d7 0x6f370bd0b6e0a5ec 0x800fffff801ffff3 0x5d7f1ff03fe0fff8

def z586 : W := mkw 0x0000000000000001 0x4007015000000000 0x8000000000000001 0x000f007000000000

def z587 : W := mkw 0x0d237fa95a41fb43 0x48b703d906f70fab 0x8003ffffffe1ffff 0x4fff03f007ff0fff

def z588 : W := mkw 0x4d23fffb7ed1fb43 0xc8bff7db47ff5fab 0xfff3ffffffffffff 0xefffffffc7ffffff

def z589 : W := mkw 0x0003defb64919240 0x0800000007ed55a8 0x0003fffffffffff0 0x0f40000007fffff8

def z590 : W := mkw 0x0000000000000000 0x0000000000000000 0x0003e0000001fc02 0x4920020004000c00

def z591 : W := mkw 0x141613a98824b2d5 0x67070951b0e2a36e 0xfc7c1ffff8ffe3ff 0xffdf3df1fbe3f3ff

def z592 : W := mkw 0xb49c8364a92ca4bd 0xe70a9965b94ae376 0xfc7c1ffff8ffe3ff 0xffdf3df1fbe3f3ff

def z593 : W := mkw 0x0000022000008001 0x4002014000400120 0x000000e380000071 0x0403004000600060

def z594 : W := mkw 0xa08a92ed21089669 0xe70f917429e8c17c 0x800c00ff801c0071 0x144f107039e0c078

def z595 : W := mkw 0x4d356f20da65e996 0x2fb0628b6657afe7 0x7ff3ffe3fffffffe 0xefb0e38fc67fffe7

def z596 : W := mkw 0x624398d264900002 0x983df6b64fad5000 0x8383fffffffe0003 0x8e3ffe3e07fff000

def z597 : W := mkw 0x000398d264900003 0xc83ff7d007ad5000 0x8003fffffffe0003 0xce3ffff007fff000

def z598 : W := mkw 0x5240000000000003 0x50376fd2d0000000 0x8070000000000003 0x403f2ff1c0000000

def z599 : W := mkw 0x14171bb2ccb4a097 0x48376d4196e73322 0x00701f0380e20380 0x00132d81c2633380

def z600 : W := mkw 0xeda96d045b496d2a 0x2fb062af6e178ed7 0xffffff007fe1fffe 0xfbf0e3fffe1f0fff

def z601 : W := mkw 0xedabfdd67fd96d2a 0xafbdf6af6fbfded7 0xffffffffffffffff 0xffffffffffffffff

def z602 : W := mkw 0xfac820041108442b 0xf73ffffef8108855 0xfffc00000001fc7f 0xf1fffffff8000c7f

def z603 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003ff1f80001f80 0x007f03b007e00f98

def z604 : W := mkw 0x524256a900019243 0x58376fd2d6e005a8 0x8073ffff8001fff3 0x4d7f2ff1c7e00ff8

def z605 : W := mkw 0xa088804421080428 0xa70890242908c054 0xff8c00fc001c0073 0xf46cd27e3980c078

def z606 : W := mkw 0x0000000000000000 0x2700000020008044 0x7c0c00000001e07c 0x7180004038000067

def z607 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x0003ffff80000383 0x0c3f018007e00380

def z608 : W := mkw 0x365403208824a095 0xf70f9d75b842a366 0xfc7c1fe3f8ffe3ff 0xff9f3df1fa63f3e7

def z609 : W := mkw 0x0001080040000002 0x0830600006050000 0x00001f0000e00000 0x0010200002030000

def z610 : W := mkw 0x000212a900009243 0x4837015006e00128 0x8003ffff80000073 0x0c7f007007e00078

def z611 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c00e0781de3ff 0xff8011c1f800c3e7

def z612 : W := mkw 0x5240000000000003 0xd03fffd2d0000000 0x0070000000000003 0x803ffd81c0000000

def z613 : W := mkw 0x141799d2ecb42096 0xaf3dfc01b7aff246 0x7c7ffffffffe000f 0xbebffc01fffff007

def z614 : W := mkw 0x4d2129005a406900 0x0080600b40170a03 0x7ff3e0007fe1fc0e 0xeba0e20fc41f0c07

def z615 : W := mkw 0x041657a98825b2d7 0x6f3703d126e2a7ee 0x8003fffff8ffffff 0x4fff03f007e3ffff

def z616 : W := mkw 0x0002108000000000 0x0005000000a00000 0x000000ff80000001 0x040f000001e00000

def z617 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff01f0000e1ff8c 0x6190238fc2030f87

def z618 : W := mkw 0x2000000000000000 0x8008902408000000 0x8380000000000000 0x002cc23e00000000

def z619 : W := mkw 0xa888a04431084428 0x8008902c09184811 0x0380000007000000 0x0000c00e001c0000

def z620 : W := mkw 0x0000000000000000 0x2700000020008044 0x000c00e0001c0071 0x140010403800c060

def z621 : W := mkw 0x0002109204900000 0x0005040000a01000 0x0000000380020000 0x00030c0000603000

def z622 : W := mkw 0x6240000000000000 0x9008f42648000000 0x0380000000000000 0x0000c00e00000000

def z623 : W := mkw 0xedabffed7b49ff6b 0xefbff3ff6fffcfff 0xfffffffffffdffff 0xfffff3ffffffcfff

def z624 : W := mkw 0x565403208824a097 0x50376fd3d0422322 0x00701f0380e20380 0x00132d81c2633380

def z625 : W := mkw 0x0001080040000000 0x0000600000050000 0x000000007fe00000 0x8200e000001f0000

def z626 : W := mkw 0x1240000000000001 0x50070d5090000000 0x0000000000000000 0x00030c0000000000

def z627 : W := mkw 0x1014022080248095 0x67020940b040a164 0x000c000000000070 0x1000004038000060

def z628 : W := mkw 0xa088804421080428 0xa70890242908c054 0x800fe0fc7f1c0073 0x9e6cd0703d9cc078

def z629 : W := mkw 0xac88a14439086428 0xa708902d291aca57 0xfffffffc7ffdffff 0xfffcf3ffff9fcfff

def z630 : W := mkw 0x0002548900011240 0x0800000006a00488 0x0003e01c00001c00 0x0040000005800c18

def z631 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003ff1f87e20000 0x003fec0007ff3000

def z632 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003e0ff80001c71 0x046f027005e00c78

def z633 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x00001fff80fe0001 0x041f3c0003e3f000

def z634 : W := mkw 0x4000000000000003 0x403763d240000000 0xfff0000000000003 0xe03fe3ffc0000000

def z635 : W := mkw 0x000290c020000002 0x883d900007a84000 0x0003ffffff1c0003 0x8e3fd00007fcc000

def z636 : W := mkw 0x000256a900019242 0x0835000006e005a8 0x0003ffff8001fff3 0x0d7f000007e00ff8

def z637 : W := mkw 0x3254022080248095 0xf70f9d74b840a164 0x800c00e3801e0071 0x140f1c703860f060

def z638 : W := mkw 0x4523ddd26ed12902 0x88bdf68347af5682 0x0073fffffffe0383 0x8e3ffd81c7fff380

def z639 : W := mkw 0x0000000000000000 0x0000000000000000 0x8003e01c00001c00 0x006c023005800c18

def z640 : W := mkw 0x10179af2e4b48097 0xef3ffd40b7edf164 0x000ffffffffe0073 0x9e3ffc403ffff060

def z641 : W := mkw 0x04179bf2ecb4a094 0x2f00000127eff366 0x0003ffffffffe3fc 0x0f80000007fff3e7

def z642 : W := mkw 0xa888a0443108442a 0xa73df42c2918c855 0xff8fe0fc7f1dfc7f 0xfffffe7e3d9ccc7f

def z643 : W := mkw 0xac9ca364b92ce4bc 0xa708902d295aeb77 0xff8fffffffffffff 0xffecd27e3fffffff

def z644 : W := mkw 0x0000462900019241 0x400203d0004005a8 0x0000000000000380 0x0000018000000380

def z645 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0x8383e0fc7f1dfc7c 0x0fecc23e059ccc7f

def z646 : W := mkw 0x0000000000000000 0x0000000000000000 0x0003e0fc00000003 0x0c2c000005800000

def z647 : W := mkw 0x49216c0052414902 0x08b0628a46150c81 0x7f83e0007f01fc0e 0xeba0c20e041c0c07

def z648 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003e01c07000003 0x803ffc00059c0000

def z649 : W := mkw 0x141403208824a095 0x4002094190422322 0x0070000000000380 0x00000181c0000380

def z650 : W := mkw 0x0400010008002000 0x0000000100020202 0x7c70000078e0000c 0xa2802001c0030007

def z651 : W := mkw 0xbc9ca364b92ce4bd 0xe70a996db95aeb77 0x7ffc1fe3ffffe3ff 0xff93fdcffa7ff3e7

def z652 : W := mkw 0xa08a90d625980428 0xa70d942429a8d054 0x800c00ff801e0071 0x144f1c7039e0f078

def z653 : W := mkw 0x141613a08824a097 0x6f370941b6e2a366 0x7c7ffffff8ffe3ff 0xffbf3dc1ffe3f3e7

def z654 : W := mkw 0x14158b72ecb4a095 0xe70afd41b14ff366 0x7c7c1fe3ffffe3ff 0xff93fdc1fa7ff3e7

def z655 : W := mkw 0xa888200411084428 0x2700002c28108855 0xff8fe0fc0001fc7f 0x7dec027e3d800c7f

def z656 : W := mkw 0xa88a76ad1109d66b 0x6f3703fc2ef08dfd 0xff8fffff8001ffff 0x7dff03fe3fe00fff

def z657 : W := mkw 0x0014022080248094 0x270000002040a164 0x000000e3801e0070 0x040000000060f060

def z658 : W := mkw 0x888af6ed3109d66b 0x6f3703d827f8cdfd 0x8003ffffff1dffff 0x4fff03f007fccfff

def z659 : W := mkw 0x765657a98825b2d7 0xff3ffff7fee2a7ee 0xfffffffff8ffffff 0xffffffffffe3ffff

def z660 : W := mkw 0xfac8a0443108442b 0xd03ffffed9184811 0xffffe01c07001c03 0xf07ffffffd9c0c18

def z661 : W := mkw 0x324256a900019243 0xd83f9ff49ee005a8 0x800fffff8001fff3 0x5d7f1ff03fe00ff8

def z662 : W := mkw 0x324398d264900003 0xd83ffd749fad5000 0x800ffffffffe0003 0x9e3ffc703ffff000

def z663 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x80001f038001fff0 0x415303f002600ff8

def z664 : W := mkw 0x8888a04431084428 0x0000000801184811 0x0003e01c07001c00 0x00400000059c0c18

def z665 : W := mkw 0x200256a900019243 0xc83f93f40ee005a8 0xff8fffff8001fff3 0xfd7fd3fe3fe00ff8

def z666 : W := mkw 0x1000000000000003 0x40370bd090000000 0xfc7c000000000003 0xf03f3ff1f8000000

def z667 : W := mkw 0x452109004a402900 0x0080600340070202 0x0070000000e00000 0x00002001c0030000

def z668 : W := mkw 0x0002108000000002 0x0835000006a00000 0x8003ffff8001fc73 0x4d7f027007e00c78

def z669 : W := mkw 0x000256a900019243 0x6f3703d026e085ec 0xfc0ffffff81dffff 0xffff13f03fe0cfff

def z670 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c000078ffe3fc 0xf3803dc1f803f3e7

def z671 : W := mkw 0x45214d004a412902 0x08b0628346070682 0x7c701f0078e1e38e 0xeb902181c2030387

def z672 : W := mkw 0x0001885264900002 0x803df400010d5000 0x000000007ffe0003 0x823ffc00001ff000

def z673 : W := mkw 0xa888662d1109d669 0x670203fc28508dfd 0xff8c00000001fffc 0x71c003fe38000fff

def z674 : W := mkw 0x000398d264900000 0x0800000007ad5000 0x0003e01c07000000 0x00000000059c0000

def z675 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x00001fe38001e3f3 0x4d1301c0026003e0

def z676 : W := mkw 0x0000000000000000 0x0000000000000000 0x7f80000000000002 0xe020c20e00000000

def z677 : W := mkw 0x0002108000000002 0x0835000006a00000 0x00001f0380000000 0x0013000002600000

def z678 : W := mkw 0xada9ed447b496d28 0xaf88902d2f1fced7 0xff8ffffc7ffdffff 0xffecd27e3f9fcfff

def z679 : W := mkw 0xa88bb8d67598442a 0xaf3df42c2fbdd855 0x7f8ffffffffe000f 0xbebffc0e3ffff007

def z680 : W := mkw 0x141657a98825b2d7 0x48370bd196e227aa 0x8073ffff80e3fff3 0x4d7f2ff1c7e33ff8

def z681 : W := mkw 0x05214d004a412900 0x0880000106070682 0x00001f0000e00380 0x0000000002030380

def z682 : W := mkw 0x1414010088242094 0x27000801b002a246 0x7c7c1fe3f8fe000f 0xbe933c01fa63f007

def z683 : W := mkw 0x4d2067291a41fb41 0x408203db40520fab 0xfff000000001fffc 0x61c003ffc0000fff

def z684 : W := mkw 0x0000000000000002 0x0035640000000000 0x0000000000000000 0x00132c0000000000

def z685 : W := mkw 0x0000000000000000 0x0000000000000000 0x00001f000001e382 0x4910018002000380

def z686 : W := mkw 0x45235fa94a41bb43 0x48b763d346e707aa 0x00701f0380e00380 0x00132181c2630380

def z687 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003ffff87000003 0x0c3fc00007fc0000

def z688 : W := mkw 0x0800200010004000 0x2700000820108845 0x7f8fe0e07f1dfc7f 0xffa0d24e3c1ccc67

def z689 : W := mkw 0x0000022000008003 0x403703d000400120 0x80001fe38001e3f3 0x4d3f03f0026003e0

def z690 : W := mkw 0x7654010088242094 0xb708fc27f802a246 0x7ffc000078fe000c 0xb280fc0ff803f007

def z691 : W := mkw 0x0803b8d274904002 0x883df40807bd5801 0x7f83fffffffffc0f 0xefbffe0e07fffc07

def z692 : W := mkw 0x141447298825b2d5 0x67020bd1b042a7ee 0xfc7c1fe3f8ffffff 0xffd33ff1fa63ffff

def z693 : W := mkw 0x4d216d005a416900 0x0880600b46170e83 0x7ff3ff007fe1ff8c 0xab80e00fc61f0f87

def z694 : W := mkw 0x4d2065001a416900 0x0080028b40120e83 0x7ff01f0078e1ff8e 0xeb90238fc2030f87

def z695 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8fe01c7f1c1c0c 0xb2ecd23e3d9ccc1f

def z696 : W := mkw 0x00039afb64909243 0xc83ff55007ed5128 0x8003fffffffe0073 0x8e7ffc7007fff078

def z697 : W := mkw 0xa88af6ed3109d66b 0xc83f93fc0ff84db9 0x8383ffff8701fff3 0x4d7fc3fe07fc0ff8

def z698 : W := mkw 0x0000022000008001 0x4002014000400120 0x00001f0380000380 0x0013018002600380

def z699 : W := mkw 0x2800200010004000 0x8008902c08100801 0xff8fe0007f01fc0f 0xfbacd27e3c1c0c07

def z700 : W := mkw 0x000290d224900000 0x0000000001a85000 0x000000ff801e0000 0x0400000001e0f000

def z701 : W := mkw 0xa889a85675984428 0xa708f42c291dd855 0x7f8c00007ffe000c 0xb280fc0e381ff007

def z702 : W := mkw 0xeac8a0443108442a 0x903df6be49184811 0x8383e01c07001c00 0x006cc23e059c0c18

def z703 : W := mkw 0xa88bfeff7599d66b 0xef3ff7fc2ffdddfd 0xff8fffffffffffff 0xfffffffe3fffffff

def z704 : W := mkw 0xa888a04431084428 0x8008902c09184811 0x8383e0fc0701fc73 0x4d6cc27e059c0c78

def z705 : W := mkw 0x41214c0042410902 0x08b0628246050480 0x0000000000000000 0x0000000000000000

def z706 : W := mkw 0x141403208824a097 0xe73ffd41b042a366 0x7c7c1fe3f8ffe3ff 0xffbffdc1fa63f3e7

def z707 : W := mkw 0x6000000000000002 0x803df6a648000000 0xfffc000000000003 0xf03ffffff8000000

def z708 : W := mkw 0x400398d264900002 0x883df68247ad5000 0x0073fffffffe0003 0x8e3ffd81c7fff000

def z709 : W := mkw 0x7240000000000000 0x90089c26d8000000 0x7ffc000000000000 0x30001c0ff8000000

def z710 : W := mkw 0x1400010008002001 0x4002094190020202 0x7c7c1fe3f8ffe38f 0xff933dc1fa63f387

def z711 : W := mkw 0x000256a900019243 0x4837015006e005a8 0x8003ffff8001fff3 0x0d7f007007e00ff8

def z712 : W := mkw 0x7240000000000000 0x9008fc26d8000000 0x7ffc000000000003 0xb02cfc0ff8000000

def z713 : W := mkw 0x0d216d005a416900 0x0880000906170e83 0x7ff3ff007fe1ff8e 0xebb0e38fc61f0f87

def z714 : W := mkw 0x600398d264900002 0x883df6a64fad5000 0xfffffffffffe0003 0xfe3ffffffffff000

def z715 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3ff007fe1ff8c 0xab90e18fc61f0f87

def z716 : W := mkw 0x724212a000008003 0xd83ffff6dee00120 0xffffffff8001e3f3 0xfd3fffffffe003e0

def z717 : W := mkw 0x000256a900019242 0x0835029006e005a8 0x8003ffff8001fff2 0x4d7c03b007e00ff8

def z718 : W := mkw 0x7240000000000002 0x9038fea6d8000000 0x7ffc000000000000 0xb020fe0ff8000000

def z719 : W := mkw 0xa88af6ed3109d66b 0xef3f93fc2ff8cdfd 0x7f8c1f03ff1c038c 0xb293d18e3a7cc387

def z720 : W := mkw 0x7240000000000002 0x903dfeb6d8000000 0xfffc000000000003 0xb03ffe3ff8000000

def z721 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc00fc00000073 0xf47ffffff9800078

def z722 : W := mkw 0x3000000000000001 0xc00a996498000000 0x7ffc000000000003 0xf013fdcff8000000

def z723 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8fe01c0701fc7f 0xf1ecd27e3d9c0c7f

def z724 : W := mkw 0x7240000000000002 0x9038fc26d8000000 0x7ffc000000000002 0xb030fc0ff8000000

def z725 : W := mkw 0x7243189244900003 0x58376ff6dea51000 0xfffc1f0380e20000 0x70132ffffa633000

def z726 : W := mkw 0x4401090048002002 0x0830628346070202 0x7ff3ff007fe1e38e 0xebb0e38fc61f0387

def z727 : W := mkw 0x8c9c2324992ce4bc 0x270000092052ab77 0x00001fe3f8fffffc 0x0fc000000263ffff

def z728 : W := mkw 0x7240000000000003 0x50320bf6d8000000 0xfffc000000000002 0x703003fff8000000

def z729 : W := mkw 0x424256a900019243 0x583767d246e005a8 0x8003ffff8001fff3 0x4d7f03f007e00ff8

def z730 : W := mkw 0x00035ea940019243 0x483763d006e505a8 0x8003ffff80e1fff3 0x4d7f23f007e30ff8

def z731 : W := mkw 0x72435ea940019243 0xd83ffff6dee505a8 0xffffffffffe1fff3 0xff7fffffffff0ff8

def z732 : W := mkw 0x7241080040000003 0xd83ffff6de050000 0xffffffe3fffe0003 0xfe3ffffffe7ff000

def z733 : W := mkw 0x325692f2a4b48095 0xf70f9d74b9e8f164 0x800c00ff801e0071 0x140f1c7039e0f060

def z734 : W := mkw 0x8da9ed447b496d2a 0xafb8f009271fced7 0x0003fffc7ffdffff 0x8ffcf000079fcfff

def z735 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003e0fffffe0001 0x862ffc0005fff000

def z736 : W := mkw 0x100256a900019243 0x48370bd096e005a8 0xfc7ffffff8fffff3 0xff7f3ff1ffe3fff8

def z737 : W := mkw 0x7243dcdb64911243 0xd83ffff6dfad5488 0xffffe01c07001c03 0xf07ffffffd9c0c18

def z738 : W := mkw 0x72435ebb44919243 0xd83ffff6dee515a8 0xfffc1f0380e20383 0xf03ffffffa633380

def z739 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c1fe3f8fe03fd 0xb6933dc1fa63f3e7

def z740 : W := mkw 0x724398d264900003 0xd83ffff6dfad5000 0x7ffffffffffe0003 0xbe3ffd8ffffff000

def z741 : W := mkw 0x7240000000000002 0x903dfeb6d8000000 0x7ffc000000000000 0xb000fc0ff8000000

def z742 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc000000000000 0x703feffff8000000

def z743 : W := mkw 0x000256a900019242 0x0835000006e005a8 0x8003ffff8001fff3 0x4d7f027007e00ff8

def z744 : W := mkw 0x400256a900019243 0x483763d246e005a8 0x8383ffff8001fff3 0x4d7fc3fe07e00ff8

def z745 : W := mkw 0x000256a900019243 0x483703d006e005a8 0xfc73ffff8001fff3 0xed7f23f1c7e00ff8

def z746 : W := mkw 0x8c9ca144b92c64bc 0x27000009211aea57 0x0003e0fc7ffffc7c 0x0fc00000059ffc7f

def z747 : W := mkw 0x7243dcd264910003 0xd83ffff6dfad5480 0xffffffffffffff83 0xff3fffffffffff80

def z748 : W := mkw 0x000398d264900002 0x0835640007ad5000 0x0003fffffffe0002 0x8e33ec0007fff000

def z749 : W := mkw 0x7240000000000003 0xd03afff6d8000000 0xfffc000000000002 0xf030fffff8000000

def z750 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003ff03fffe0002 0x8a33fc00067ff000

def z751 : W := mkw 0xe5a9cd446b492d2a 0xafb8f2a76f0fc6d6 0x807c1ffc00fc03f1 0x145c31f1fb83c3f8

def z752 : W := mkw 0x14165589882532d6 0x2f350a91b6a2a6ce 0xfc7fe01c78fe1c0c 0xb2ec3e31fd83fc1f

def z753 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc000000000003 0xf02cd3fff8000000

def z754 : W := mkw 0x4003dcd264910002 0x883df68247ad5480 0x7ff3ffffffffff83 0xef3fff8fc7ffff80

def z755 : W := mkw 0x7240804020000000 0x9008fc26d9084000 0x7fffe0fc7f1c0003 0xbe2cfc0ffd9cc000

def z756 : W := mkw 0x7241080040000003 0xd83ffff6de050000 0xffffe00007000003 0xf03ffffffc1c0000

def z757 : W := mkw 0x000256bb04919243 0x483707d006e015a8 0x8003ffff8003fff3 0x4d7f0ff007e03ff8

def z758 : W := mkw 0x7240000000000003 0x50376ff6d8000000 0x7ffc000000000000 0x30132d8ff8000000

def z759 : W := mkw 0x7240000000000000 0x10000826d8000000 0xfffc000000000000 0x7000027ff8000000

def z760 : W := mkw 0x000256a900019243 0x483767d006e005a8 0x8003ffff8001fff3 0x4d7f2ff007e00ff8

def z761 : W := mkw 0x3000804020000001 0xc00a996499084000 0xfffffffffffe0003 0xfe3ffffffffff000

def z762 : W := mkw 0x300398d264900003 0xc83ffd649fad5000 0xfffffffffffe0003 0xfe3ffffffffff000

def z763 : W := mkw 0x7240440000010002 0x9838fea6de000480 0x7fffff000001ff82 0xf930ff8ffe000f80

def z764 : W := mkw 0x7241885264900000 0x9008fc26d90d5000 0x7ffc000007000000 0xb000fc0ff81c0000

def z765 : W := mkw 0x000256a900019243 0x483763d006e005a8 0x8003ffff8001fff3 0xcd7fe3f007e00ff8

def z766 : W := mkw 0xbc9ca364b92ce4bd 0xc00a996d995a6b33 0x83f3ff1f87e21f80 0x007fefbfc7ff3f98

def z767 : W := mkw 0x5000000000000001 0x40026942d0000000 0x7ffc000000000003 0xf013fdcff8000000

def z768 : W := mkw 0x000398d264900002 0x883d940007ad5000 0x0003fffffffe0003 0x0e3f1c0007fff000

def z769 : W := mkw 0x0001885264900000 0x8008f400010d5000 0x000000e3fffe0001 0x8603fc00007ff000

def z770 : W := mkw 0x0001ce7b64919241 0xc00af7d0014d55a8 0x800000007ffffff0 0xc340fff0001ffff8

def z771 : W := mkw 0x4d22f5d23ed16900 0x808d968b41ba5e83 0x7ff000ff801fff8d 0x658f1f8fc1e0ff87

def z772 : W := mkw 0x500256a900019243 0x48376bd2d6e005a8 0xffffffff8001fff3 0xfd7fffffffe00ff8

def z773 : W := mkw 0x000398d264900000 0x880d940007ad5000 0x0003fffffffe0003 0x8e1f3c0007fff000

def z774 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x7f83fffffffe0003 0xee3ffe0e07fff000

def z775 : W := mkw 0x7240000000000001 0xd00ffd76d8000000 0x7ffc000000000000 0xb003fc0ff8000000

def z776 : W := mkw 0x4d216d005a416900 0x0880600b46170e83 0x7ff3ff007fe1ff8e 0xeb90e18fc61f0f87

def z777 : W := mkw 0x52435ebb44919243 0x58376fd2d6e515a8 0x8073ffff80e3fff3 0x4d7f2ff1c7e33ff8

def z778 : W := mkw 0x000398d264900000 0x8808900007ad5000 0x0003fffffffe0003 0x8e3ffc0007fff000

def z779 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003ff1ffffe0000 0x823ffc0007fff000

def z780 : W := mkw 0x0001885264900000 0x00000000010d5000 0x00001fe3fffe0003 0x8e133c00027ff000

def z781 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc000000000002 0xf03ce3fff8000000

def z782 : W := mkw 0x7240000000000002 0x903dfc26d8000000 0x7ffc000000000000 0xb013fc0ff8000000

def z783 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x7c03ffffffffe00f 0xefbffc0007fff007

def z784 : W := mkw 0x59356e20d265c997 0x6fb26bcaf655ade5 0x038fe0e3871e1c71 0x1423de4e3c7cfc60

def z785 : W := mkw 0x7240000000000000 0x900dfc36d8000000 0xfffc000000000000 0xb00cfc3ff8000000

def z786 : W := mkw 0x7240000000000003 0xd03f9bf6d8000000 0xfffc000000000003 0xf03fd3fff8000000

def z787 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c1fe3f8ffe3fc 0xbf933d81fa63f3e7

def z788 : W := mkw 0x7243defb64919243 0xd83ffff6dfed55a8 0xfffffffffffe0383 0xfe3ffffffffff380

def z789 : W := mkw 0x141403208824a095 0x67020941b042a366 0x007c1fe3f8ffe3fd 0x1f933dc1fa63f3e7

def z790 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8fe0ffff1ffc7f 0xffefde7e3dfcfc7f

def z791 : W := mkw 0x7242109204900003 0xd03ffff6d8a01000 0xfffc000380020003 0xf03ffffff8603000

def z792 : W := mkw 0x0000804020000000 0x8008900001084000 0x00001fe3fffe0003 0x8e13fc00027ff000

def z793 : W := mkw 0x7240804020000001 0xd00a9bf6d9084000 0xffffe0fc7f1c0003 0xfe2cd3fffd9cc000

def z794 : W := mkw 0x7240000000000001 0xd00afd66d8000000 0x7ffc000000000001 0xb003fc4ff8000000

def z795 : W := mkw 0x724398d264900003 0xd83ffff6dfad5000 0xffffe01c7ffe0003 0xf23ffffffd9ff000

def z796 : W := mkw 0x0003dcdb64911242 0x883df40007ad5488 0x0003fffffffe1c03 0x8e7ffc0007fffc18

def z797 : W := mkw 0x7241885264900001 0xd00afd66d90d5000 0x7ffc1fe3fffe0003 0xfe13fdcffa7ff000

def z798 : W := mkw 0x724398d264900003 0xd83ffff6dfad5000 0xffffffff87000003 0xfc3ffffffffc0000

def z799 : W := mkw 0x72435ebb44919243 0xd83ffff6dee515a8 0xffffffff80e3fff3 0xfd7fffffffe33ff8

def z800 : W := mkw 0x8da9a9447b486d28 0x27800009211fca57 0x000000007ffc000c 0x02800000001fc007

def z801 : W := mkw 0x724398d264900003 0xd83ffff6dfad5000 0xffffe0ff871e0003 0xf43ffffffdfcf000

def z802 : W := mkw 0x724398d264900003 0xd83ffff6dfad5000 0xffffff1c7fe00003 0xfa3fffffff9f0000

def z803 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff01f007fe1ff8c 0xe390e38fc21f0f87

def z804 : W := mkw 0x141403208824a095 0x67020941b042a366 0xfc7c1ffff8ffe3ff 0xffdf3df1fbe3f3ff

def z805 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xffffe0007f000003 0xfa3ffffffc1c0000

def z806 : W := mkw 0x8c9fbbf6fdbce4be 0xaf3df40927fffb77 0x0003ffffffffffff 0x8ffffc0007ffffff

def z807 : W := mkw 0x0000440000010003 0x483703d006000480 0x8003fffc0001fff3 0x4d7f03f007800ff8

def z808 : W := mkw 0x0003dcd264910002 0x883df68007ad5480 0x8003fffffffffff3 0xcf7ffff007fffff8

def z809 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc000000000003 0x703fc3fff8000000

def z810 : W := mkw 0x7242548900011243 0xd83ffff6dea00488 0xffffff1c0001ff83 0xf97fffffff800f98

def z811 : W := mkw 0x0000804020000002 0x803df40001084000 0x0003fffffffe0003 0x8e3ffc0007fff000

def z812 : W := mkw 0x4d216d095a417b42 0x08b0629b46170e8b 0xfff3ff007fe1ff8e 0xebf0e3bfc61f0f9f

def z813 : W := mkw 0x0d352900da646994 0x278000092017aa47 0x000000007ffe000c 0x02800000001ff007

def z814 : W := mkw 0x724256a900019243 0x58370bf6dee005a8 0xfffc1f0380000380 0x701303fffa600380

def z815 : W := mkw 0x4d2065001a416902 0x00b0628b40120e83 0x7ff3e0007f01ff8e 0xebb0e38fc41c0f87

def z816 : W := mkw 0x000256a900019242 0x0835029006e005a8 0x8003ffff8001fff3 0x4d6c027007e00ff8

def z817 : W := mkw 0x0000022000008003 0x403703d000400120 0x8003ffff8001fff3 0x4d7f03f007e00ff8

def z818 : W := mkw 0x424398d264900002 0x983df69247ad5000 0x0003fffffffe0003 0x8e3ffc0007fff000

def z819 : W := mkw 0x4d237d925ed16902 0x08b5668b46b71e83 0x7ff3ffe3ffffff8f 0xefb3ff8fc67fff87

def z820 : W := mkw 0x4d216d005a416900 0x0080628b40170e83 0x7ff3e0007fe1ff8e 0xeba0e38fc41f0f87

def z821 : W := mkw 0x724398d264900003 0xd83ffff6dfad5000 0xfffc1f03fffe0003 0xf23ffffffa7ff000

def z822 : W := mkw 0xb09e92eda12c96fd 0xe70f9974b9e8e17c 0x800c00ff801e0071 0x144f1c7039e0f078

def z823 : W := mkw 0x4d237d895a417b42 0x08b5629b46b70e8b 0x7ff3ff007fe1ff8e 0xebb0e38fc61f0f87

def z824 : W := mkw 0x7240000000000001 0x50020976d8000000 0xfffc000000000000 0x3000007ff8000000

def z825 : W := mkw 0x0d3467209a65e994 0x278000092052afe7 0x00001fe3f8fffffc 0x0f8000000263ffe7

def z826 : W := mkw 0x7240000000000000 0x9008feb6d8000000 0xfffc000000000000 0xb000fe3ff8000000

def z827 : W := mkw 0x000290d224900000 0x800d940001a85000 0x0003fffffffe0003 0x8e3ffc0007fff000

def z828 : W := mkw 0x7240000000000002 0x903dfeb6d8000000 0xfffc000000000002 0xf03cffbff8000000

def z829 : W := mkw 0x724256a900019240 0x9808fc26dee005a8 0x7fffffff8001fff0 0xbd40fc0fffe00ff8

def z830 : W := mkw 0x724256a900019241 0x58020bf6dee005a8 0xffffffff8001fff0 0x7d4003ffffe00ff8

def z831 : W := mkw 0x724256a900019243 0xd83ffff6dee005a8 0xffffe01c0001fff3 0xf17ffffffd800ff8

def z832 : W := mkw 0x100256a900019243 0x48370bd096e005a8 0xfc7fffff8001fff3 0x7d7f03f1ffe00ff8

def z833 : W := mkw 0x7240000000000001 0x50020bf6d8000000 0xfffc000000000002 0xf01023fff8000000

def z834 : W := mkw 0x7240000000000003 0xd03affe6d8000000 0x7ffc000000000003 0xf033ffcff8000000

def z835 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003ffff8001fff3 0xcd7f3ff007e00ff8

def z836 : W := mkw 0x4d2129005a406902 0x08b0600b46170a03 0x7ff3ff007fe1e38e 0xebb0e18fc61f0387

def z837 : W := mkw 0x7240022000008001 0x50020bf6d8400120 0xfffc1fe38001e3f3 0x7d1303fffa6003e0

def z838 : W := mkw 0x624398d264900002 0x983df4264fad5000 0x0383fffffffe0003 0x8e3ffc0e07fff000

def z839 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x7c0ffffffffe0003 0xfe3ffc403ffff000

def z840 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003ffffffffe383 0xcf3ffd8007fff380

def z841 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003ffff8001fff0 0x4d6c03f007e00ff8

def z842 : W := mkw 0x724290d224900001 0xd00f9ff6d9a85000 0xfffc00ff801e0001 0x740f1ffff9e0f000

def z843 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003ffff8001fff1 0x0d5f01f007e00ff8

def z844 : W := mkw 0x3f616d005a416901 0xd88f9d7d9e170e83 0x800fff007fe1ff8d 0x1b8f1c703e1f0f87

def z845 : W := mkw 0x724290d224900003 0xd03ffff6d9a85000 0xffffe0ffff1e0003 0xfe3ffffffdfcf000

def z846 : W := mkw 0x7240000000000002 0x9038fea6d8000000 0xfffc000000000003 0xf03cfffff8000000

def z847 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff01f007fe0038e 0xe2b0e38fc21f0387

def z848 : W := mkw 0x000256a900019242 0x0835029006e005a8 0x8003e01c0001fff0 0x016c023005800ff8

def z849 : W := mkw 0x124256a900019243 0x58370fd096e005a8 0x8003ffff8001fff3 0x4d7f0ff007e00ff8

def z850 : W := mkw 0x200398d264900002 0x883df4240fad5000 0x7f8ffffffffe0003 0xbe3ffc0e3ffff000

def z851 : W := mkw 0x0d356f20da65e996 0x2fb060092657afe7 0x0003ffe3ffffffff 0x8fb3fc00067fffe7

def z852 : W := mkw 0x7240440900011243 0xd03ffff6d8000488 0xfffc000000001c03 0xf07ffffff8000c18

def z853 : W := mkw 0x000398d264900002 0x0835000007ad5000 0x0003fffffffe0003 0x8e3f3c0007fff000

def z854 : W := mkw 0x7240000000000000 0x900dfc26d8000000 0x7ffc000000000001 0xb00ffc0ff8000000

def z855 : W := mkw 0xbc9c2324992ce4bd 0x6702096db852ab77 0x7ffc00000001e3fc 0x718001cff80003e7

def z856 : W := mkw 0x0002548900011242 0x0835029006a00488 0x8003fffc0001fff3 0x4d7c03f007800ff8

def z857 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3ff007fe01f8c 0xa2b0e38fc61f0f87

def z858 : W := mkw 0x0003dcd264910002 0x883df40007ad5480 0x0003ffffffffff83 0x8f3ffc0007ffff80

def z859 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x8003fffffffe0073 0x8e7ffc7007fff078

def z860 : W := mkw 0xe9abfcd677d94d2a 0x88bdf6ae4fbd5c91 0x8383e01c07001c00 0x006cc23e059c0c18

def z861 : W := mkw 0x5240000000000003 0x50376fd2d0000000 0x7ffc000000000003 0xf033ffcff8000000

def z862 : W := mkw 0x8c9ef7edb92df6ff 0x6f3703d927faefff 0x8003ffffffffffff 0x4fff03f007ffffff

def z863 : W := mkw 0x200398d264900002 0x883df4240fad5000 0xff8ffffffffffc73 0xff7ffe7e3ffffc78

def z864 : W := mkw 0x7240000000000000 0x90089826d8000000 0x7ffc000000000000 0xb000d00ff8000000

def z865 : W := mkw 0x7240000000000001 0x50020bf6d8000000 0xfffc00000001fc70 0x714003fff8000c78

def z866 : W := mkw 0x4000000000000002 0x0030628240000000 0x7ffc000000000003 0xf030f3cff8000000

def z867 : W := mkw 0x7240000000000001 0xd00ffff6d8000000 0xfffc000000000001 0xf00ffffff8000000

def z868 : W := mkw 0x7240000000000001 0xd00afd66d8000000 0xfffc000000000003 0xf03ffffff8000000

def z869 : W := mkw 0x7240000000000003 0x50326bf6d8000000 0xfffc000000000000 0x7020c3fff8000000

def z870 : W := mkw 0x7241080040000003 0xd83ffff6de050000 0xfffc1f0000e00003 0xf03ffffffa030000

def z871 : W := mkw 0x8da8e5443b496d28 0x27800009211aced7 0x0003e0fc7f1dfffc 0x0fc00000059ccfff

def z872 : W := mkw 0x7240000000000001 0xd00a9bf6d8000000 0xfffc000000000000 0xf000d3fff8000000

def z873 : W := mkw 0x7240000000000000 0x9008fc26d8000000 0x7ffc000000000000 0x3000c00ff8000000

def z874 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8fe0fc071dfc7d 0x75ecd27e3d9ccc7f

def z875 : W := mkw 0x0001080040000002 0x883df40006050000 0x0003ffe3fffe0003 0x8e3ffc00067ff000

def z876 : W := mkw 0x4d237d805a416902 0x08b0628b46b70e83 0x7ff3ffffffe1ff8e 0xefb0e38fc7ff0f87

def z877 : W := mkw 0x4d2129005a406902 0x00b0628b40170a03 0x7ff01f007fe1e38e 0xebb0e38fc21f0387

def z878 : W := mkw 0x4c00210018006002 0x0030628b40120a03 0x7ff3ff007fe1ff8e 0xebb0e38fc61f0f87

def z879 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8fe0fc7ffffc7f 0xffecfe7e3d9ffc7f

def z880 : W := mkw 0x57635fa94a41bb43 0x58b76fd3d6e707aa 0x00701f0380e00380 0x00132d81c2630380

def z881 : W := mkw 0x7240000000000001 0xd00afd66d8000000 0x7ffc000000000000 0xf000fdcff8000000

def z882 : W := mkw 0x7240000000000002 0x903dfea6d8000000 0x7ffc000000000003 0xf03fff8ff8000000

def z883 : W := mkw 0x0800200010004000 0x2700000820108845 0xff8fe0fc7f1dfc7f 0xffecd27e3d9ccc7f

def z884 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3ff0007e1ff8c 0x61b0e38fc61f0f87

def z885 : W := mkw 0x14179bf2ecb4a097 0xef3ffd41b7eff366 0x7c7fe01c0701e3fc 0x71acc1c1fd9c03e7

def z886 : W := mkw 0x6000000000000000 0x800892a648000000 0xfffc000000000003 0xf02cd3fff8000000

def z887 : W := mkw 0x5000000000000001 0x40020bc2d0000000 0x7ffc000000000000 0x700003cff8000000

def z888 : W := mkw 0x000256a900019241 0x400703d000e005a8 0x8000001c0001fff0 0x414c03f001800ff8

def z889 : W := mkw 0x000398d264900002 0x0830600007ad5000 0x0003fffffffe0003 0x8e33fc0007fff000

def z890 : W := mkw 0x7240022900009243 0xd03ffff6d8400128 0xfffc000000000073 0xf07ffffff8000078

def z891 : W := mkw 0x7240000000000001 0xd00ffd76d8000000 0xfffc000000000003 0xf01ffdfff8000000

def z892 : W := mkw 0x4d237d895a417b42 0x08b0628b46b70e8b 0x7ff3ff1c7fe1ff8e 0xebf0e38fc79f0f9f

def z893 : W := mkw 0x5d3423209a64e995 0x6782094bf052ab67 0x7ffc00000001e3fc 0x718001cff80003e7

def z894 : W := mkw 0x724290d224900000 0x900dfc26d9a85000 0x7ffc00ff801e0001 0xb40ffc0ff9e0f000

def z895 : W := mkw 0x4d237d895a417b42 0x08b5629b46b70e8b 0xfff3ffffffe1ff8f 0xefffe3bfc7ff0f9f

def z896 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc000000000000 0xf013fffff8000000

def z897 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8fe0fc0701fc7f 0x7decc27e3d9c0c7f

def z898 : W := mkw 0x724398d264900002 0x983dfeb6dfad5000 0xfffffffffffe0003 0xbe3ffe3ffffff000

def z899 : W := mkw 0x8c9ca144b92c64bc 0x27000009211aea57 0x000000007ffe000c 0x02800000001ff007

def z900 : W := mkw 0x7240000000000003 0x50326bf6d8000000 0xfffc000000000003 0xf033fffff8000000

def z901 : W := mkw 0x6b63fcd276d14902 0x98bdf6be4fbd5c81 0x8383e01c07001c00 0x002cc23e059c0c00

def z902 : W := mkw 0x7240000000000000 0x10000aa6d8000000 0x7ffc000000000000 0x7000038ff8000000

def z903 : W := mkw 0x6000000000000000 0x8008f02648000000 0x7ffc000000000000 0xb000f00ff8000000

def z904 : W := mkw 0x7240022900009241 0x50020bf6d8400128 0xfffc000000000070 0x704003fff8000078

def z905 : W := mkw 0x7240000000000003 0xd03afbf6d8000000 0xfffc000000000003 0xf03cf3fff8000000

def z906 : W := mkw 0xac88a14439086428 0xa708902d291aca57 0x7ffc00007ffc000c 0xb280f00ff81fc007

def z907 : W := mkw 0x4d2129005a406900 0x0080600b40170a03 0x7ff000007fe1e38c 0xe380e18fc01f0387

def z908 : W := mkw 0x724398d264900003 0xd83ffff6dfad5000 0xfffc1fff80fe0003 0xf43ffffffbe3f000

def z909 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc1fe380000003 0xfc3ffffffa600000

def z910 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc000078fe0003 0xf23ffffff803f000

def z911 : W := mkw 0x4800640010014002 0x0830628a46100c81 0x7ff3ff007f01ff8e 0xebb0e38fc61c0f87

def z912 : W := mkw 0x000398d264900002 0x0835640007ad5000 0x0003fffffffe0003 0x0e3f2c0007fff000

def z913 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc1f0078e00003 0xfa3ffffffa030000

def z914 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc00e3801e0003 0xf43ffffff860f000

def z915 : W := mkw 0x0001080040000000 0x0800000006050000 0x0003ffe3fffe0003 0x8e133c00067ff000

def z916 : W := mkw 0x72414c0040010003 0xd83ffff6de050480 0xffffff007fe1ff83 0xfb3ffffffe1f0f80

def z917 : W := mkw 0x2800200010004000 0x8008902c08100801 0xff8fe0fc7f01fc7f 0xffecd27e3d9c0c7f

def z918 : W := mkw 0x0000462900019241 0x400203d0004005a8 0x8003ffff8001fff3 0x4d7f03f007e00ff8

def z919 : W := mkw 0x000256a900019243 0x483703d006e005a8 0xff83ffff8001fff3 0xed7fc3fe07e00ff8

def z920 : W := mkw 0x724256a900019243 0xd83ffff6dee005a8 0xfffc1fff800003f3 0xf47ffffffbe003f8

def z921 : W := mkw 0x0d3467209a65e994 0x278000092052afe7 0x000000000001fffc 0x0180000000000fe7

def z922 : W := mkw 0x7241884060000003 0xd83ffff6df0d4000 0xfffffffc7ffc0003 0xfe3fffffff9fc000

def z923 : W := mkw 0xbc9da956fdbc64bc 0xa708fc2db91ffa57 0x7ffc00007ffe000c 0xb280fc0ff81ff007

def z924 : W := mkw 0x5000000000000001 0x40020bc2d0000000 0x7ffc000000000003 0xf0133fcff8000000

def z925 : W := mkw 0x000256a900019241 0x480203d006e005a8 0x8003ffff8001fff3 0x4d6c03f007e00ff8

def z926 : W := mkw 0x5001080040000003 0x48326bc2d6050000 0x7fffffe3fffe0003 0xfe33ffcffe7ff000

def z927 : W := mkw 0x7240000000000001 0xd00afff6d8000000 0xfffc000000000003 0xf02cfffff8000000

def z928 : W := mkw 0x724292fb24909243 0xd03ffff6d9e85128 0xfffc00ff801e0073 0xf47ffffff9e0f078

def z929 : W := mkw 0x4d233ba95a40fb41 0x4087615b40f70b2b 0xfff000ffffe0007d 0xa6cfe07fc1ff007f

def z930 : W := mkw 0x00035ebb44919243 0x483703d006e515a8 0x8003ffff80e3fff3 0x4d7f03f007e33ff8

def z931 : W := mkw 0x7240000000000001 0xd00a9bf6d8000000 0xfffc000000000000 0x702cc3fff8000000

def z932 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7ffffff8ffe3ff 0xffbf3dc1ffe3f3e7

def z933 : W := mkw 0x7243defb64919243 0xd83ffff6dfed55a8 0xffffffff8701fff3 0xfd7ffffffffc0ff8

def z934 : W := mkw 0xb09c8264a12c84bd 0xe70a9964b948e174 0x000c00e3801e0071 0x14031c403860f060

def z935 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8ffffffffffc7f 0xffecd27e3ffffc7f

def z936 : W := mkw 0x0003dcdb64911242 0x883df69007ad5488 0x8003ffffffffff83 0xcf7fffb007ffff98

def z937 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3ff000701ff8e 0x69b0c38fc61c0f87

def z938 : W := mkw 0x0d356f20da65e994 0x2f8000092657afe7 0x0003ff007fe1fffc 0x0b800000061f0fe7

def z939 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc00e00001e073 0xfd3ffffff8000060

def z940 : W := mkw 0x724256a900019243 0xd83f9ff6dee005a8 0xffffffff8001fff3 0x7d7f1fffffe00ff8

def z941 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0x83fc000000000001 0x103ffffff8000000

def z942 : W := mkw 0xa888200411084428 0x2700002c28108855 0xff8fe0fc7f01fc7f 0xffecc27e3d9c0c7f

def z943 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003fffff81dfff3 0xcf7f13f007e0cff8

def z944 : W := mkw 0x000212a000008003 0x4837014006e00120 0x8003ffff8001fff3 0x4d7f03f007e00ff8

def z945 : W := mkw 0x724398d264900001 0x58020bf6dfad5000 0xfffffffffffe0000 0x7e0003fffffff000

def z946 : W := mkw 0x400256a900019243 0x483703d246e005a8 0xfff3ffff8001fff3 0x6d7f03ffc7e00ff8

def z947 : W := mkw 0x0c00650018016002 0x0830028906120e83 0x7ff3ff007fe1ff8e 0xebb0e38fc61f0f87

def z948 : W := mkw 0x0d356f20da65e997 0x6fb203c92657afe7 0x0003ffe3ffffffff 0x4fb303c0067fffe7

def z949 : W := mkw 0x7240000000000001 0x50020bf6d8000000 0x7ffc000000000000 0x3000018ff8000000

def z950 : W := mkw 0x7241885264900000 0x9008fc26d90d5000 0xffffe0fc7ffe0003 0xfe2cfe7ffd9ff000

def z951 : W := mkw 0x8c9ca364b92ce4bc 0xa7089009215aeb77 0x0003ffffffffffff 0x8ffffc0007ffffff

def z952 : W := mkw 0x724290d224900003 0xd03ffff6d9a85000 0xfffc1ffff8fe0003 0xfe3ffffffbe3f000

def z953 : W := mkw 0xdac8a0443108442b 0x77376fdaf118c855 0x0073e0fc7f1dfc7c 0x0fd32d81c59ccc7f

def z954 : W := mkw 0x0000000000000000 0x0000000000000000 0x0003ffe3fffe0003 0x8e33fc00067ff000

def z955 : W := mkw 0x7240000000000002 0x903dfc26d8000000 0xfffc000000000003 0xf03ffe7ff8000000

def z956 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x8003fffffffe1c03 0x8e7ffe3007fffc18

def z957 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003fffff8e1fff3 0xcf7f23f007e30ff8

def z958 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc000000000001 0x701f3ffff8000000

def z959 : W := mkw 0xa88b38965598442a 0x2f35642c2eb59855 0xff8c1f0380e3fc7c 0x71d32e7e3a633c7f

def z960 : W := mkw 0x4d237d895a417b42 0x08b5629b46b70e8b 0xfff3fffc7fe1ffff 0xeffce3ffc79f0fff

def z961 : W := mkw 0x3000000000000000 0x8008982498000000 0xfffc000000000003 0xf02cfe7ff8000000

def z962 : W := mkw 0x7240000000000001 0x50020bf6d8000000 0xfffc000000000003 0x702c03fff8000000

def z963 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8fe0fc7f1dfc7f 0xfffffe7e3d9ccc7f

def z964 : W := mkw 0x7240000000000001 0xd00a9bf6d8000000 0xfffc000000000003 0xf03ffffff8000000

def z965 : W := mkw 0x000256a900019243 0x403703d000e005a8 0x800000ff8001fff3 0x457f03f001e00ff8

def z966 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3ff007fe0038e 0xaab0e18fc61f0387

def z967 : W := mkw 0x55375fa9ca65bbd7 0x48b76bd3d6e727aa 0x00701f0380e20380 0x00132d81c2633380

def z968 : W := mkw 0x4d2129005a406900 0x0080600b40170a03 0x7ff3ff007fe1ff8e 0xebb0e38fc61f0f87

def z969 : W := mkw 0x8dabffed7b49ff6b 0x6fb703d927ffcfff 0x8003fffffffdffff 0x4fff03f007ffcfff

def z970 : W := mkw 0x7242548900011243 0xd83ffff6dea00488 0xffffffff80001c03 0xfc7fffffffe00c18

def z971 : W := mkw 0x7240000000000000 0x9008fc26d8000000 0xffffe0fc0001fc73 0xfd6cfe7ffd800c78

def z972 : W := mkw 0x724398d264900003 0xd83ffd66dfad5000 0x7ffffffffffe0003 0xfe3ffdcffffff000

def z973 : W := mkw 0xac9ca144b92c64bc 0xa708902d291aea57 0x7f8c00007ffe000c 0xb280d00e381ff007

def z974 : W := mkw 0x7240022000008003 0xd03ffff6d8400120 0xfffc00e380000073 0xf43ffffff8600060

def z975 : W := mkw 0x6000000000000003 0xc03ff3f648000000 0xfffc000000000003 0xf03ff3fff8000000

def z976 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003ff1f8001fff0 0x417f03f007e00ff8

def z977 : W := mkw 0x7240000000000003 0x50376ff6d8000000 0xfffc000000000002 0xf033effff8000000

def z978 : W := mkw 0x40035ea940019243 0x483763d246e505a8 0xfff3ffffffe1fff3 0xef7fe3ffc7ff0ff8

def z979 : W := mkw 0x4123dcd266d10902 0x88bdf68247ad5480 0x0003fffffffe0003 0x8e3ffc0007fff000

def z980 : W := mkw 0x141403208824a095 0x67020941b042a366 0xfc7c1fe3f8ffe3ff 0xffbf3ff1fa63f3e7

def z981 : W := mkw 0xf2c880442108042b 0xd03ffff6d9084010 0xfffc001c00000003 0xf07ffffff9800018

def z982 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3fffc7fe1ff8f 0xefbce38fc79f0f87

def z983 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc000000000000 0xb03fffbff8000000

def z984 : W := mkw 0x724398d264900003 0xd03ffff6d9ad5000 0xfffc00fffffe0003 0xf63ffffff9fff000

def z985 : W := mkw 0x7241080040000003 0x58326bf6de050000 0xffffff007fe00002 0xfa30e3fffe1f0000

def z986 : W := mkw 0x0d377fa9da65fbd7 0x6fb703d926f7afef 0x8003ffffffffffff 0x4fff03f007ffffff

def z987 : W := mkw 0x000398d264900000 0x0805040007ad5000 0x0003fffffffe0000 0x0e030c0007fff000

def z988 : W := mkw 0x72439af264908003 0xd83ffff6dfed5120 0xffffffffffffe3f3 0xff3ffffffffff3e0

def z989 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3ff007fe1ff8c 0x6ba0c38fc61f0f87

def z990 : W := mkw 0x0002548000010002 0x0835028006a00480 0x8003ffff8001fff3 0x4d7f03f007e00ff8

def z991 : W := mkw 0x200398d264900002 0x883df4240fad5000 0x8383fffffffe0003 0x8e3ffe3e07fff000

def z992 : W := mkw 0x7240000000000003 0x50370bf6d8000000 0xfffc000000000000 0x702c03fff8000000

def z993 : W := mkw 0x7240000000000001 0xd00a9ff6d8000000 0xfffc000000000000 0x70001ffff8000000

def z994 : W := mkw 0x7240000000000000 0x9008fc26d8000000 0x7ffc000078fe0000 0xb200fc0ff803f000

def z995 : W := mkw 0x7240462900019241 0xd00afff6d84005a8 0xfffc00000001fff0 0xf140fffff8000ff8

def z996 : W := mkw 0x000398d264900002 0x803df40001ad5000 0x000000fffffe0003 0x863ffc0001fff000

def z997 : W := mkw 0x7241885264900002 0x9838fea6df0d5000 0x7fffff007ffe0002 0xfa30ff8ffe1ff000

def z998 : W := mkw 0x7240462900019241 0x50020bf6d84005a8 0xfffc000000000380 0x700003fff8000380

def z999 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003ff1c0001fff2 0x497c03f007800ff8

def z1000 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003fffffffe0001 0x0e2fdc0007fff000

def z1001 : W := mkw 0x000398d264900000 0x880df40007ad5000 0x0003fffffffe0001 0x8e0ffc0007fff000

def z1002 : W := mkw 0x7242548900011243 0xd83ffff6dea00488 0xffffe0fc0001fc73 0xfd7ffffffd800c78

def z1003 : W := mkw 0x4d216d005a416900 0x0880628b46170e83 0x7ff3ff007fe1ff8c 0xeb80e38fc61f0f87

def z1004 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8fffffff1dfc7f 0xffffd27e3ffccc7f

def z1005 : W := mkw 0x8c9c2324992ce4bc 0x270000092052ab77 0x000000000001fffc 0x01c0000000000fff

def z1006 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0x7ffc000000000002 0xf033ff8ff8000000

def z1007 : W := mkw 0x6243dcdb64911242 0x983df6b64fad5488 0x8383fffffffe1c03 0x8e7ffe3e07fffc18

def z1008 : W := mkw 0x4d216d005a416900 0x0080628b40170e83 0x7ff000000701ff8c 0x6180c38fc01c0f87

def z1009 : W := mkw 0x000256a900019243 0x483703d006e005a8 0xfc03fffff801ffff 0xefff03f007e00fff

def z1010 : W := mkw 0x7240000000000002 0x903dfeb6d8000000 0xfffc000000000003 0xf02cfe7ff8000000

def z1011 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7ffffff8ffffff 0xffd33dc1ffe3ffff

def z1012 : W := mkw 0x7243189244900002 0x983dfc26dea51000 0x7ffc1f0380e20000 0xb013fc0ffa633000

def z1013 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3ff03ffe3ff8e 0xebb3ef8fc67f3f87

def z1014 : W := mkw 0x00035ebb44919243 0x483767d006e515a8 0x8003ffff8001fff3 0x4d7f03f007e00ff8

def z1015 : W := mkw 0x7240000000000001 0xd00f9ff6d8000000 0xfffc000000000000 0x700c03fff8000000

def z1016 : W := mkw 0x3000000000000003 0xc03f9bf498000000 0xfffc000000000003 0xf03ffffff8000000

def z1017 : W := mkw 0x724398d264900003 0xd83ffff6dfad5000 0xffffe01c07000000 0x702cc3fffd9c0000

def z1018 : W := mkw 0xfdbda944fb6c6dbc 0xa788f82ff91fea57 0x7ffc00007ffe000c 0xb280fc0ff81ff007

def z1019 : W := mkw 0x7240000000000003 0x50370bf6d8000000 0xfffc000000000003 0xf03f3ffff8000000

def z1020 : W := mkw 0xa888a05635984428 0xa708942c2918d855 0xff8fe0fc7f1ffc7f 0xffecde7e3d9cfc7f

def z1021 : W := mkw 0x7242108000000003 0xd83ffff6dea00000 0xfffffffff8fe0003 0xfe3fffffffe3f000

def z1022 : W := mkw 0x3000022000008001 0xc00a996498400120 0xffffffff8001fff3 0xfd7fffffffe00ff8

def z1023 : W := mkw 0x1414010088242094 0x27000801b002a246 0x7c7c1fe3f8ffe38f 0xff933d81fa63f387

def z1024 : W := mkw 0xb09c8264a12c84bd 0xe70a9964b948e174 0x800c00fc001c0071 0x144c10703980c078

def z1025 : W := mkw 0x1d3467209a65e995 0x67820949b052afe7 0x7c7c00000001fffc 0x718001c1f8000fe7

def z1026 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc000000000001 0xb01ffdfff8000000

def z1027 : W := mkw 0x4d216d005a416900 0x0080628b40170e83 0x7ff01f007fe1ff8e 0xeb90e38fc21f0f87

def z1028 : W := mkw 0x7242108000000003 0xd03ffff6d8a00000 0xfffc00ff80000003 0xf43ffffff9e00000

def z1029 : W := mkw 0x8da865041b496d28 0x2780000920128ed7 0x000000000001fffc 0x01c0000000000fff

def z1030 : W := mkw 0x724256a900019243 0xd83ffff6dee005a8 0xffffe0ff80001c73 0xf47ffffffde00c78

def z1031 : W := mkw 0x0000462900019240 0x00000000004005a8 0x8003e0fc0001fff3 0x4d6c027005800ff8

def z1032 : W := mkw 0x724256a900019243 0xd83f9bf6dee005a8 0xffffffff8001fff3 0xfd7fd3ffffe00ff8

def z1033 : W := mkw 0x0d216d005a416900 0x2f80000926178ec7 0x0003ffe07ffdfffc 0x0f800000061fcfe7

def z1034 : W := mkw 0x9c9c2324992ce4bd 0x67020949b052ab77 0x7c7c00000001fffc 0x71c001c1f8000fff

def z1035 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3ffe3ffe1ff8f 0xefb3e38fc67f0f87

def z1036 : W := mkw 0x7240000000000003 0x50376ff6d8000000 0xfffc000000000003 0x703f2ffff8000000

def z1037 : W := mkw 0x100256a900019243 0x48370bd096e005a8 0x800fffff8001fff3 0x5d7f1ff03fe00ff8

def z1038 : W := mkw 0x4d216d005a416900 0x0080628b40170e83 0x7ff000007fe0038c 0xa280e18fc01f0387

def z1039 : W := mkw 0x665403208824a096 0xb73df6b76842a366 0x83801fe3f8ffe3fc 0x0facc23e0263f3e7

def z1040 : W := mkw 0x8dabffed7b49ff68 0x2f80000927ffcfff 0x0003fffffffdfffc 0x0fc0000007ffcfff

def z1041 : W := mkw 0x0000022000008001 0x4002014000400120 0x8003e0fc0001fff3 0x4d6c03f005800ff8

def z1042 : W := mkw 0x3000000000000000 0x8008982498000000 0x7ffc000000000000 0xb000fc0ff8000000

def z1043 : W := mkw 0x7242548900011243 0x58370bf6dea00488 0xffffe01c00001c00 0x706c03fffd800c18

def z1044 : W := mkw 0x7240000000000001 0xd00ffd76d8000000 0xfffc000000000003 0xf02ffe7ff8000000

def z1045 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0xfff3ff007fe1ff8f 0xebbce3ffc61f0f87

def z1046 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003fffffffffc73 0x8f7ffc0007fffc78

def z1047 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c1f03f8fe038f 0xf2933dc1fa63f387

def z1048 : W := mkw 0x7240000000000001 0xd00f9ff6d8000000 0xfffc000000000003 0xf01f3ffff8000000

def z1049 : W := mkw 0x624398d264900002 0x983df6b64fad5000 0xfff3fffffffe0003 0xee3fffbfc7fff000

def z1050 : W := mkw 0x7240804020000003 0xd03ffff6d9084000 0xfffc00007f1c0003 0xf23ffffff81cc000

def z1051 : W := mkw 0x724256a900019243 0xd83ffff6dee005a8 0xffffffff8001fff3 0x7d7fc3ffffe00ff8

def z1052 : W := mkw 0x7240462900019243 0xd03ffff6d84005a8 0xfffc1fe38001fff3 0xfd7ffffffa600ff8

def z1053 : W := mkw 0x8c9ca364b92ce4bc 0x27000009215aeb77 0x0003e0fc7f1dfffc 0x0fc00000059ccfff

def z1054 : W := mkw 0x0000462900019243 0x483203d0064005a8 0x8003fffc0001fff3 0x4d7c03f007800ff8

def z1055 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0x7ffc000000000003 0xf013fdcff8000000

def z1056 : W := mkw 0x6000000000000002 0x003062a648000000 0xfffc000000000002 0xf030e3fff8000000

def z1057 : W := mkw 0x000256a900019241 0x4802014006e005a8 0x8003ffff8001fff3 0x4d7f03f007e00ff8

def z1058 : W := mkw 0x724256a900019243 0xd83ffff6dee005a8 0xffffff038001ff83 0xf93ffffffe600f80

def z1059 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc00000001fc73 0xf17ffffff8000c78

def z1060 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7fffe3ffffe3ff 0xffb3fdc1fe7ff3e7

def z1061 : W := mkw 0x141403208824a095 0x67020941b042a366 0xfc7c1fe3f8ffffff 0xffd33ff1fa63ffff

def z1062 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8fe0fc7f1c1c7d 0xb6ecd27e3d9ccc7f

def z1063 : W := mkw 0x724398d264900001 0xd00ffd76d9ad5000 0xfffc00fffffe0001 0xb60ffc7ff9fff000

def z1064 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x00001fe3fffe0003 0x8e13fc00027ff000

def z1065 : W := mkw 0x7240022000008001 0xd00afd66d8400120 0x7ffc1fe38001e3f3 0xfd13fdcffa6003e0

def z1066 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003e0ff8001fff1 0x456f03f005e00ff8

def z1067 : W := mkw 0x0d37fff2fef5e996 0xafbdf40927ffffe7 0x0003ffffffffffff 0x8fbffc0007ffffe7

def z1068 : W := mkw 0x5d3467299a65fbd5 0x67820bdbf052afef 0xfffc00000001fffc 0x71c003fff8000fff

def z1069 : W := mkw 0x7240000000000000 0x9008fc26d8000000 0x7ffc000000000003 0xb013fc0ff8000000

def z1070 : W := mkw 0x4d216d125ed16902 0x08b0668b46171e83 0x7ff3ff007fe3ff8e 0xebb0ef8fc61f3f87

def z1071 : W := mkw 0x7240000000000001 0x50020bf6d8000000 0xffffe0fc0001fc73 0x7d6c03fffd800c78

def z1072 : W := mkw 0x300256a900019243 0xc83f9bf49ee005a8 0xffffffff8001fff3 0xfd7fffffffe00ff8

def z1073 : W := mkw 0x0000462900019241 0x400203d0004005a8 0x8003e01c0001fff0 0x416c03f005800ff8

def z1074 : W := mkw 0x000256a900019240 0x0800000006e005a8 0x8003ffff8001fff0 0x0d6c023007e00ff8

def z1075 : W := mkw 0x724256a900019243 0x58376ff6dee005a8 0xfffc1f038001fff0 0x71532ffffa600ff8

def z1076 : W := mkw 0x5000462000018003 0x48326bc2d64005a0 0x7fffffe38001fff3 0xfd33ffcffe600fe0

def z1077 : W := mkw 0x8dbdef64fb6dedbc 0x2f800009275feff7 0x0003fffffffffffc 0x0fc0000007ffffff

def z1078 : W := mkw 0x73614c0042410903 0xd8bffff6de050480 0xfffc000000000003 0xf03ffffff8000000

def z1079 : W := mkw 0x5000000000000003 0xc03fffc2d0000000 0x7ffc000000000003 0xf03fffcff8000000

def z1080 : W := mkw 0x00035ea940019243 0x483763d006e505a8 0x8003ffff8701fff3 0x4d7fc3f007fc0ff8

def z1081 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003ffff80001ff1 0x047f03f007e00ff8

def z1082 : W := mkw 0x4d2065001a416902 0x08b0028b46120e83 0x7ff3ff007f01ff8e 0xebb0c38fc61c0f87

def z1083 : W := mkw 0x7241080040000002 0x9838fc26de050000 0x7fffff007fe00002 0xba30fc0ffe1f0000

def z1084 : W := mkw 0x0d37fff2fef5e994 0x2f80000927ffffe7 0x0003fffffffffffc 0x0f80000007ffffe7

def z1085 : W := mkw 0x0000440000010000 0x0000028000000480 0x8003e0fc0001fff3 0x4d6c03f005800ff8

def z1086 : W := mkw 0x41235ea942419b43 0x48b763d246e505a8 0x8003ffff8001fff3 0x4d7f03f007e00ff8

def z1087 : W := mkw 0xfedc2324992ce4bd 0x77020bfff852ab77 0xfffc00000001fffc 0x71c003fff8000fff

def z1088 : W := mkw 0x7240440000010003 0xd83ffff6de000480 0xfffffffc0001fff3 0xfd7fffffff800ff8

def z1089 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x8003fffffffe0003 0xce3ffe7007fff000

def z1090 : W := mkw 0x6000000000000002 0x8038f2a648000000 0x7ffc000000000002 0xf030f38ff8000000

def z1091 : W := mkw 0x4d216d005a416900 0x0880028b46170e83 0x7ff3ff007fe1ff8e 0xeba0c38fc61f0f87

def z1092 : W := mkw 0x000256a900019241 0x4007015000e005a8 0x800000ff8001fff1 0x054f007001e00ff8

def z1093 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8fe01c7f1dfc7c 0xf3ecd27e3d9ccc7f

def z1094 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x00001ffffffe0001 0x861ffc0003fff000

def z1095 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c1f03f8ffe38e 0xfb933d81fa63f387

def z1096 : W := mkw 0x7240462900019241 0x50020bf6d84005a8 0xfffc1fe38001fff3 0xfd533ffffa600ff8

def z1097 : W := mkw 0x8c9ca364b92ce4bc 0x27000009215aeb77 0x00001fe3ffffe3fc 0x0f800000027ff3e7

def z1098 : W := mkw 0x3000000000000001 0x4002096498000000 0xfffc000000000000 0x700003fff8000000

def z1099 : W := mkw 0x00035ea940019243 0x483763d006e505a8 0x8003fffffffffff3 0xcf7ffff007fffff8

def z1100 : W := mkw 0x7240000000000001 0xd00afff6d8000000 0xfffc000000000000 0x7000c3fff8000000

def z1101 : W := mkw 0x7240440000010003 0xd83ffff6de000480 0xfffc1f0000000383 0xf03ffffffa000380

def z1102 : W := mkw 0x7240462900019243 0x58326bf6de4005a8 0xffffff000001fff2 0xf970e3fffe000ff8

def z1103 : W := mkw 0x0400010008002000 0x2700000120028246 0x7c7c1fe3f8ffe3ff 0xff933dc1fa63f3e7

def z1104 : W := mkw 0x000256a900019242 0x0835029006e005a8 0x8003ffff8001fff3 0x0d7f023007e00ff8

def z1105 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3ffe07fe1ffff 0xefb0e3cfc61f0fe7

def z1106 : W := mkw 0x7240000000000000 0x10000826d8000000 0x7ffc000000000000 0xb0003c0ff8000000

def z1107 : W := mkw 0x7240000000000001 0x50020bf6d8000000 0xfffc1fe3f8fe0003 0xfe133ffffa63f000

def z1108 : W := mkw 0xeda9a9567fd86d28 0xa788f42f691fda57 0x7ffc00007ffe000c 0xb280fc0ff81ff007

def z1109 : W := mkw 0x7240804020000003 0xd03ffff6d9084000 0xfffffffffffe0003 0xfe3ffffffffff000

def z1110 : W := mkw 0x200398d264900002 0x883df4240fad5000 0x800ffffffffe0003 0x9e3ffc703ffff000

def z1111 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xffffe0fc00000003 0xfc3ffffffd800000

def z1112 : W := mkw 0x7240022000008003 0xd03ffff6d8400120 0xfffc1fe3f8ffe3f3 0xff3ffffffa63f3e0

def z1113 : W := mkw 0x7240804020000003 0xd03ffff6d9084000 0xffffe0fc7f1dfc73 0xff7ffffffd9ccc78

def z1114 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8ffffc7ffdfc7f 0xfffcf27e3f9fcc7f

def z1115 : W := mkw 0x7243189244900003 0xd83ffff6dea51000 0xfffc1fe3f8fe0003 0xfe3ffffffa63f000

def z1116 : W := mkw 0x00035ebb44919243 0x483767d006e515a8 0x8003fffff8fffff3 0xcf7f3ff007e3fff8

def z1117 : W := mkw 0x0c1423209824e094 0x270000092052ab67 0x0003ffe3fffffffc 0x0f800000067fffe7

def z1118 : W := mkw 0x724398d264900003 0xd83ffff6dfad5000 0x7ffc1f03fffe0000 0xb213fd8ffa7ff000

def z1119 : W := mkw 0xfedca144b92c64bc 0xb708fc2ff91aea57 0x7ffc00007ffe000c 0xb280fc0ff81ff007

def z1120 : W := mkw 0x7240805224900003 0xd03ffff6d9085000 0xfffc0000001e0003 0xf03ffffff800f000

def z1121 : W := mkw 0x7240000000000000 0x10006c26d8000000 0x7ffc000000000000 0x30002c0ff8000000

def z1122 : W := mkw 0x7000000000000003 0xc03afbe6d8000000 0xfffc000000000003 0xf03ffffff8000000

def z1123 : W := mkw 0x724212a900009241 0xd00ffd76d8e00128 0xfffc00ff80000071 0xb44ffc7ff9e00078

def z1124 : W := mkw 0x000398d264900000 0x0800000007ad5000 0x0003fffffffe0001 0x0e031c0007fff000

def z1125 : W := mkw 0x7240000000000001 0xd00afff6d8000000 0xfffc000000000003 0xf013fffff8000000

def z1126 : W := mkw 0x7241885264900001 0xd00afff6d90d5000 0xfffc00007ffe0000 0xf200fffff81ff000

def z1127 : W := mkw 0x7240000000000003 0x50376bf6d8000000 0xfffc000000000003 0xf03fe3fff8000000

def z1128 : W := mkw 0x000398db64901242 0x883df41007ad5008 0x8003fffffffe0003 0x8e7ffc3007fff018

def z1129 : W := mkw 0x0001884060000002 0x8838f000070d4000 0x0003fffffffe0003 0x8e3ffc0007fff000

def z1130 : W := mkw 0x7243189244900003 0xd83ffff6dea51000 0xffffff03ffe20003 0xfa3ffffffe7f3000

def z1131 : W := mkw 0x7240000000000001 0x50020bf6d8000000 0xfffc000000000001 0x70031ffff8000000

def z1132 : W := mkw 0x7240000000000000 0x90089826d8000000 0xfffc000000000003 0xf02cd27ff8000000

def z1133 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0x7ffc000000000003 0xb03ffd8ff8000000

def z1134 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x80001fff8001fff1 0x455f03f003e00ff8

def z1135 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xffffe0fc7f1dfc7f 0xfffcf3fffd9ccc7f

def z1136 : W := mkw 0x724398d264900003 0xd83ffff6dfad5000 0xffffff1f87e20003 0xf03fffffffff3000

def z1137 : W := mkw 0x7240000000000001 0xd00a9bf6d8000000 0xfffc000000000001 0x700c13fff8000000

def z1138 : W := mkw 0x8c9ef7edb92df6fc 0x2f00000927faefff 0x0003fffffffffffc 0x0fc0000007ffffff

def z1139 : W := mkw 0x7242548900011243 0xd83ffff6dea00488 0xfffc000000000003 0xf03ffffff8000000

def z1140 : W := mkw 0x400398d264900002 0x883df40247ad5000 0x7ff3fffffffe0003 0xae3ffc0fc7fff000

def z1141 : W := mkw 0x000398d264900002 0x0835640007ad5000 0x00001f03fffe0000 0x02132c00027ff000

def z1142 : W := mkw 0x724398d264900002 0x983dfc26dfad5000 0x7fffe01c07000000 0xb02cfc0ffd9c0000

def z1143 : W := mkw 0x000398d264900000 0x800df40001ad5000 0x00000003fffe0000 0x8203fc00007ff000

def z1144 : W := mkw 0x7242108900001243 0xd03ffff6d8a00008 0xfffc001c00000003 0xf07ffffff9800018

def z1145 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0xfff3ff1c7fe1ff8e 0xebfce3bfc79f0f9f

def z1146 : W := mkw 0x000256a900019241 0x400703d000e005a8 0x8003e0ff8001fff3 0x4d6f03f005e00ff8

def z1147 : W := mkw 0xb2dc8264a12c84bd 0xf70f9d74b948e174 0x800c00ff801e0071 0x144f1c7039e0f078

def z1148 : W := mkw 0x5000000000000003 0x40376bd2d0000000 0xfffc000000000003 0xf03ffffff8000000

def z1149 : W := mkw 0x4d237d805a416902 0x08b5628b46b70e83 0xfff3ffffffe1ffff 0xefffe3ffc7ff0fff

def z1150 : W := mkw 0x4d237d805a416902 0x08b5628b46b70e83 0x7ff3ff1c7fe1ff8e 0xebbce38fc79f0f87

def z1151 : W := mkw 0x7240440000010001 0x50020bf6d8000480 0xfffc00000001ff80 0x710003fff8000f80

def z1152 : W := mkw 0x724256a900019243 0xd83ffff6dee005a8 0xfffffffff8fffff3 0xff7fffffffe3fff8

def z1153 : W := mkw 0x724290c020000003 0xd83ffff6dfa84000 0xffffffffff1c0003 0xfe3ffffffffcc000

def z1154 : W := mkw 0x7240000000000003 0x50376ff6d8000000 0xfffc000000000000 0x700003fff8000000

def z1155 : W := mkw 0x4d237d925ed16902 0x08b5668b46b71e83 0x7ff3ffffffe3ff8f 0xefbfef8fc7ff3f87

def z1156 : W := mkw 0x4d2065001a416900 0x0080028b40120e83 0x7ff000007f01ff8c 0xe380c38fc01c0f87

def z1157 : W := mkw 0xbc9ca144b92c64bc 0xa708982db91aea57 0x7ffc00007f1c000c 0xb280d00ff81cc007

def z1158 : W := mkw 0x0c00210018006000 0x0000000900120a03 0x7ff3e0007f01ff8e 0xeba0c38fc41c0f87

def z1159 : W := mkw 0x7240000000000001 0x50020bf6d8000000 0xfffc000000000002 0xf020c3fff8000000

def z1160 : W := mkw 0x7240022000008003 0xd03ffff6d8400120 0xffffffff8001fff3 0xfd7fffffffe00ff8

def z1161 : W := mkw 0x7242108000000003 0x58370bf6dea00000 0xffffffff80000003 0x7c3f03ffffe00000

def z1162 : W := mkw 0x724256a900019243 0xd03ffff6d8e005a8 0xfffc00ff8001fff3 0xf57ffffff9e00ff8

def z1163 : W := mkw 0x7242108000000003 0xd83ffff6dea00000 0xffffffff8001fc73 0xfd7fffffffe00c78

def z1164 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003ffff87fe0001 0x043ffc0007fff000

def z1165 : W := mkw 0x000256a900019243 0x483703d006e005a8 0xfc0fffff8001fff3 0xfd7f13f03fe00ff8

def z1166 : W := mkw 0x0d377fa9da65fbd4 0x2f80000926f7afef 0x0003fffffffffffc 0x0fc0000007ffffff

def z1167 : W := mkw 0x7241885264900003 0xd03ffff6d90d5000 0xffffe0fc7ffe0003 0xfe3ffffffd9ff000

def z1168 : W := mkw 0x524256a900019243 0x58370bd2d6e005a8 0x8073ffff8001fff3 0x4d7f03f1c7e00ff8

def z1169 : W := mkw 0x8da9ed447b496d2a 0x2fb00289271fced7 0x8003fffc7ffdffff 0x4ffc03f0079fcfff

def z1170 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc000000000001 0xb02ffe7ff8000000

def z1171 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0x838fe0fc7f1dfc7d 0x1fecd27e3d9ccc7f

def z1172 : W := mkw 0x7241885264900003 0xd03ffff6d90d5000 0xfffc1fe3fffe0003 0xfe3ffffffa7ff000

def z1173 : W := mkw 0x724212a900009241 0x50070bf6d8e00128 0xfffc00ff80000071 0x744f03fff9e00078

def z1174 : W := mkw 0x7240000000000003 0xd83ffff6de000000 0xffffff0000000003 0xf83ffffffe000000

def z1175 : W := mkw 0x7240462900019243 0xd03ffff6d84005a8 0xfffc000000000383 0xf03ffffff8000380

def z1176 : W := mkw 0x7240000000000000 0x9008fea6d8000000 0x7ffc000000000000 0xf000ff8ff8000000

def z1177 : W := mkw 0xb2ca92ed21089669 0xf70f9d74b9e8c17c 0x800c00ff801c0071 0x144f1c7039e0c078

def z1178 : W := mkw 0x7240000000000003 0x50370bf6d8000000 0xfffc000000000000 0x701303fff8000000

def z1179 : W := mkw 0x7240000000000003 0x50376ff6d8000000 0xfffc000000000003 0xf0133ffff8000000

def z1180 : W := mkw 0x7240805224900000 0x9008fc26d9085000 0x7ffc0000001e0000 0xb000fc0ff800f000

def z1181 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003fffffffe0000 0x0e3fec0007fff000

def z1182 : W := mkw 0x7240022000008001 0x50020bf6d8400120 0xfffc00000001e3f0 0x710003fff80003e0

def z1183 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7fffe3f8ffffff 0xffb33fc1fe63ffe7

def z1184 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3ffe3ffffff8e 0xefb0e38fc67fff87

def z1185 : W := mkw 0x4d216d005a416902 0x08b5668b46170e83 0x7ff3ff007fe1ff8e 0xebb3ef8fc61f0f87

def z1186 : W := mkw 0x4d2129005a406900 0x0080600b40170a03 0x7ff01f007fe0038c 0xa290e18fc21f0387

def z1187 : W := mkw 0x6001884060000002 0x8838f2a64f0d4000 0xfffffffc7ffc0003 0xfe3cf3ffff9fc000

def z1188 : W := mkw 0x7240000000000003 0xd03ffd76d8000000 0xfffc000000000003 0xb03ffc7ff8000000

def z1189 : W := mkw 0xada9a9447b486d28 0xa788902d291fca57 0x7f8c00007ffc000c 0xb280d00e381fc007

def z1190 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3fffc7fe1fffe 0xeff0e38fc79f0fff

def z1191 : W := mkw 0x7240000000000000 0x10006826d8000000 0x7ffc000000000000 0xb000e00ff8000000

def z1192 : W := mkw 0x8dabfdd67fd96d28 0x2f80000927bfded7 0x0003fffffffffffc 0x0fc0000007ffffff

def z1193 : W := mkw 0x724212a900009243 0xd83ffff6dee00128 0xffffffff80000073 0xfc7fffffffe00078

def z1194 : W := mkw 0x7240000000000000 0x9008fc26d8000000 0x7ffc000000000002 0xf010fd8ff8000000

def z1195 : W := mkw 0x4d237d805a416902 0x08b5628b46b70e83 0x7ff3ff03ffe1ff8e 0xebb3e38fc67f0f87

def z1196 : W := mkw 0x7240440000010003 0xd83ffff6de000480 0xffffe00000001c03 0xf03ffffffc000c00

def z1197 : W := mkw 0x7240000000000001 0x50070ff6d8000000 0xfffc000000000000 0x70030ffff8000000

def z1198 : W := mkw 0x000398d264900000 0x880d940007ad5000 0x0003fffffffe0003 0x8e2fdc0007fff000

def z1199 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xffffe01c00001c03 0xf07ffffffd800c18

def z1200 : W := mkw 0x7240000000000001 0x50026bf6d8000000 0xfffc000000000000 0xf000e3fff8000000

def z1201 : W := mkw 0x724290d224900003 0xd83ffff6dfa85000 0xffffffff801e0003 0xfc3fffffffe0f000

def z1202 : W := mkw 0x7240462900019241 0xd00a9bf6d84005a8 0xffffe0fc0001fff3 0xfd6cd3fffd800ff8

def z1203 : W := mkw 0x600256a900019243 0xc83ff3f64ee005a8 0xffffffff8001fff3 0xfd7ff3ffffe00ff8

def z1204 : W := mkw 0x724398d264900000 0x9808fc26dfad5000 0x7ffffffffffe0000 0xbe00fc0ffffff000

def z1205 : W := mkw 0x8da9ed447b496d28 0x2f800009271fced7 0x0003ff007ffdff8c 0x0b800000061fcf87

def z1206 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3ff007fe1ff8f 0xebb3ff8fc61f0f87

def z1207 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003e01c0001fff3 0x417f03f005800ff8

def z1208 : W := mkw 0x000256a900019241 0x400703d000e005a8 0x80001fff8001fff3 0x4d5f03f003e00ff8

def z1209 : W := mkw 0x000398d264900000 0x800d940001ad5000 0x000000fffffe0001 0x060f1c0001fff000

def z1210 : W := mkw 0x724398d264900003 0xd83ffff6dfad5000 0xffffe0fc7f1c0003 0xfe3ffffffd9cc000

def z1211 : W := mkw 0x6000440000010002 0x8838f2a64e000480 0xfffffffc0001fff3 0xfd7cf3ffff800ff8

def z1212 : W := mkw 0x724290d224900003 0xd03ffff6d9a85000 0xfffc001c00000003 0xf03ffffff9800000

def z1213 : W := mkw 0x7240000000000001 0xd00afff6d8000000 0x7ffc000000000000 0xb000fd8ff8000000

def z1214 : W := mkw 0xa08b98d66598042a 0x883df4240fad5010 0x8003fffffffe0003 0x8e7ffc3007fff018

def z1215 : W := mkw 0x5000000000000000 0x00006802d0000000 0x7ffc000000000000 0xb000fc0ff8000000

def z1216 : W := mkw 0x3000000000000001 0xc00a996498000000 0xfffc000000000003 0xf02cd3fff8000000

def z1217 : W := mkw 0x7243dcdb64911243 0xd83ffff6dfad5488 0xfffffffffffe1c03 0xfe7ffffffffffc18

def z1218 : W := mkw 0x0000462900019241 0x400203d0004005a8 0x800000fc0001fff1 0x454c03f001800ff8

def z1219 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003ffff801ffff3 0x4d7f1ff007e0fff8

def z1220 : W := mkw 0x7240462900019243 0xd03ffff6d84005a8 0xffffe0fc0001fff3 0xfd7ffffffd800ff8

def z1221 : W := mkw 0x0003188040000002 0x0835600006a50000 0x0003fffffffe0003 0x8e3ffc0007fff000

def z1222 : W := mkw 0x000398d264900002 0x883df68007ad5000 0x0003fffffffe0003 0xce3fff8007fff000

def z1223 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003fffffffe0000 0x8e13fc0007fff000

def z1224 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7ffc1fe3f8ffe3ff 0xffb3ffcffa63f3e7

def z1225 : W := mkw 0x7240000000000000 0x9008fc26d8000000 0xfffc000000000000 0xf000fe7ff8000000

def z1226 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c1fe3f8fe038f 0xbe933d81fa63f387

def z1227 : W := mkw 0x000398d264900000 0x800df40001ad5000 0x00001ffffffe0003 0x8e1ffc0003fff000

def z1228 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003ffff80e3fff3 0x4d7f2ff007e33ff8

def z1229 : W := mkw 0x0001885264900000 0x8008f400010d5000 0x00001f03fffe0000 0x8213fc00027ff000

def z1230 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c1fe380ffe3fd 0x75933dc1fa63f3e7

def z1231 : W := mkw 0x724212a900009243 0xd03ffff6d8e00128 0xffffe0ff8001fc73 0xfd7ffffffde00c78

def z1232 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc1f0380e20003 0xf03ffffffa633000

def z1233 : W := mkw 0x500398d264900003 0xc83fffc2d7ad5000 0x7ffffffffffe0003 0xfe3fffcffffff000

def z1234 : W := mkw 0x724398d264900002 0x983dfeb6dfad5000 0xffffe01c7ffe0000 0xb22cfe3ffd9ff000

def z1235 : W := mkw 0x7240000000000002 0x903dfc26d8000000 0x7ffc000000000000 0xb02cfc0ff8000000

def z1236 : W := mkw 0x7241080040000003 0xd03ffff6d8050000 0xfffc00007fe00003 0xf23ffffff81f0000

def z1237 : W := mkw 0x7240000000000002 0x903dfeb6d8000000 0xfffc000000000000 0x302cc23ff8000000

def z1238 : W := mkw 0x724256a900019243 0x58370bf6dee005a8 0xffffffff8001fff3 0xfd7f3fffffe00ff8

def z1239 : W := mkw 0x1000000000000001 0x4002094090000000 0x7ffc000000000003 0xf033ffcff8000000

def z1240 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0xfff3ff007fe1fffe 0xebf0e3ffc61f0fff

def z1241 : W := mkw 0x724398d264900002 0x983dfea6dfad5000 0x7ffffffffffe0003 0xfe3fff8ffffff000

def z1242 : W := mkw 0x0c01290058006002 0x0830600906170a03 0x7ff3ff007fe1ff8e 0xebb0e38fc61f0f87

def z1243 : W := mkw 0x4d2065001a416900 0x0080028b40120e83 0x7ff3ff007fe1ff8e 0xebb0e38fc61f0f87

def z1244 : W := mkw 0x6240000000000002 0x903df6b648000000 0xfffc000000000003 0xf03cf3fff8000000

def z1245 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc000000000000 0xf02cfffff8000000

def z1246 : W := mkw 0x0003dcd264910002 0x883df68007ad5480 0x0003fffffffe1c03 0x8e3ffe0007fffc00

def z1247 : W := mkw 0x4d216d005a416902 0x08b5629b46170e83 0xfff3ff007fe1ff8e 0xebbce3bfc61f0f87

def z1248 : W := mkw 0x72439afb64909243 0xd83ffff6dfed5128 0xfffffffffffe0073 0xfe7ffffffffff078

def z1249 : W := mkw 0x00035ea940019243 0x483703d006e505a8 0x8003ffffffe1fff3 0x4f7f03f007ff0ff8

def z1250 : W := mkw 0x0001885264900002 0x803df400010d5000 0x00001fe3fffe0003 0x8e3ffc00027ff000

def z1251 : W := mkw 0x0000462900019243 0x403703d0004005a8 0x8003e0fc0001fff3 0x4d7f03f005800ff8

def z1252 : W := mkw 0x000290c020000002 0x883d900007a84000 0x0003fffffffe0003 0x8e3ffc0007fff000

def z1253 : W := mkw 0x724256a900019243 0x58376ff6dee005a8 0xffffffff8001fff3 0x7d7f2fffffe00ff8

def z1254 : W := mkw 0xfdbc67249b6dedbd 0x67820beff852aff7 0xfffc00000001fffc 0x71c003fff8000fff

def z1255 : W := mkw 0x7242548900011242 0x983dfeb6dea00488 0xffffe01c00001c00 0xb06cfe3ffd800c18

def z1256 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003e0fc0001fff3 0x4d6c03f005800ff8

def z1257 : W := mkw 0x6000000000000000 0x000002a648000000 0xfffc000000000000 0x700003fff8000000

def z1258 : W := mkw 0x0d352b20da64e994 0x278000092057ab67 0x00001fe3ffffe3fc 0x0f800000027ff3e7

def z1259 : W := mkw 0x7242d6e920019243 0xd83ffff6dfe845a8 0xffffffffff1dfff3 0xff7ffffffffccff8

def z1260 : W := mkw 0x7240000000000001 0xd00afd76d8000000 0xfffc000000000000 0xb000fc7ff8000000

def z1261 : W := mkw 0x4d237d925ed16902 0x08b0628b46b71e83 0x7ff3ff03ffe3ff8e 0xebb0e38fc67f3f87

def z1262 : W := mkw 0x724256a900019243 0xd83ffff6dee005a8 0xffffffff80000383 0xfc3fffffffe00380

def z1263 : W := mkw 0x000256a900019240 0x0805001006e005a8 0x8003ffff8001fff0 0x0d4c003007e00ff8

def z1264 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc000000000001 0x702fdffff8000000

def z1265 : W := mkw 0x2000000000000000 0x8008902408000000 0xfffc000000000003 0xf03cf3fff8000000

def z1266 : W := mkw 0x7242108000000003 0xd83ffff6dea00000 0xffffe01c00000003 0xf03ffffffd800000

def z1267 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3e0000701ff8e 0xe1b0e38fc41c0f87

def z1268 : W := mkw 0x1c1423209824e095 0x67020949b052ab67 0x7ffc00000001fffc 0x718003cff8000fe7

def z1269 : W := mkw 0x7240000000000003 0x50326bf6d8000000 0xfffc000000000000 0x701023fff8000000

def z1270 : W := mkw 0x4d216d005a416902 0x08b5628b46170e83 0x7ff3ff007fe1ff8f 0xebbfe38fc61f0f87

def z1271 : W := mkw 0x7240000000000000 0x10000ab6d8000000 0xfffc000000000000 0x3000023ff8000000

def z1272 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8fe01c7f01fc7e 0xfbecc27e3d9c0c7f

def z1273 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003ffffff01fff3 0xcf7fc3f007fc0ff8

def z1274 : W := mkw 0x0001885264900000 0x8008f400010d5000 0x0003fffffffe0003 0x8e3ffc0007fff000

def z1275 : W := mkw 0x524256a900019243 0x58376fd2d6e005a8 0xfff3ffff8001fff3 0xed7fefffc7e00ff8

def z1276 : W := mkw 0x7242108000000003 0xd83ffff6dea00000 0xfffc1f0380000003 0xf03ffffffa600000

def z1277 : W := mkw 0x7240000000000001 0x50020bf6d8000000 0xfffc000000000000 0xf0003ffff8000000

def z1278 : W := mkw 0x224398d264900002 0x983df4340fad5000 0x8003fffffffe0003 0x8e3ffc3007fff000

def z1279 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003ffff8001fff0 0x0d7f03b007e00ff8

def z1280 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc1f000001e383 0xf93ffffffa000380

def z1281 : W := mkw 0x7240462900019243 0xd83ffff6de4005a8 0xffffff000001fff3 0xf97ffffffe000ff8

def z1282 : W := mkw 0x000398d264900000 0x0800000007ad5000 0x0003fffffffe0000 0x0e132c0007fff000

def z1283 : W := mkw 0x4f616d005a416902 0x18b5669b46170e83 0x7ff3ff007fe1ff8e 0xebb0e38fc61f0f87

def z1284 : W := mkw 0x7241081244900003 0xd03ffff6d8051000 0xfffc000000e20003 0xf03ffffff8033000

def z1285 : W := mkw 0x6000000000000000 0x8008f02648000000 0xfffc000000000003 0xf02cf27ff8000000

def z1286 : W := mkw 0x3000000000000001 0x4002096498000000 0xfffc000000000003 0xf0133ffff8000000

def z1287 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003fffffffe0001 0x0e1f3c0007fff000

def z1288 : W := mkw 0x7240000000000001 0x50026ff6d8000000 0xfffc000000000000 0x70002ffff8000000

def z1289 : W := mkw 0x000256a900019241 0x480703d006e005a8 0x8003ffff8001fff1 0x4d4f03f007e00ff8

def z1290 : W := mkw 0x7240804020000000 0x9008fc26d9084000 0x7ffc00007f1c0000 0xb200fc0ff81cc000

def z1291 : W := mkw 0x0000440000010000 0x0800000006000480 0x8003fffc0001fff3 0x4d6c027007800ff8

def z1292 : W := mkw 0x724398d264900002 0x983dfc26dfad5000 0xfffffffffffe0003 0xfe3ffe7ffffff000

def z1293 : W := mkw 0x3240000000000001 0xd00f9d7498000000 0xfffc000000000003 0xf03ffffff8000000

def z1294 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7fffff007fe1ff8f 0xfbb0f3cffe1f0f87

def z1295 : W := mkw 0x7240000000000000 0x9008fc26d8000000 0xfffc000000000000 0xb02cfe3ff8000000

def z1296 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x03f3ff007fe1ff8c 0x0bb0e38fc61f0f87

def z1297 : W := mkw 0x0000022000008000 0x0000000000400120 0x8003ffff8001fff3 0x4d6c027007e00ff8

def z1298 : W := mkw 0x724256a900019243 0xd83ffff6dee005a8 0xfffc1fe38001e3f3 0xfd3ffffffa6003e0

def z1299 : W := mkw 0x3000000000000003 0xc03ffd6498000000 0xfffc000000000003 0xf03ffffff8000000

def z1300 : W := mkw 0xeda8a1443b486d28 0xa788902f691aca57 0x7ffc00007f1c000c 0xb280d00ff81cc007

def z1301 : W := mkw 0xffe9a9447b486d28 0xb788fc2ff91fca57 0x7ffc00007ffc000c 0xb280fc0ff81fc007

def z1302 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc00e0781c0003 0xfe3ffffff800c000

def z1303 : W := mkw 0x7241080040000000 0x9008fc26d8050000 0x7ffc00007fe00000 0xb200fc0ff81f0000

def z1304 : W := mkw 0x724212a900009243 0xd03ffff6d8e00128 0xfffc1fff8001e3f3 0xfd7ffffffbe003f8

def z1305 : W := mkw 0x7240000000000002 0x9038fea6d8000000 0x7ffc000000000000 0xb010fd8ff8000000

def z1306 : W := mkw 0x7240440000010003 0xd03ffff6d8000480 0xfffc00000001ff83 0xf13ffffff8000f80

def z1307 : W := mkw 0x7240804020000003 0xd03ffff6d9084000 0xfffc00fc001c0003 0xf43ffffff980c000

def z1308 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3e0007fe1ff8c 0xe3a0e38fc41f0f87

def z1309 : W := mkw 0x7240022000008003 0xd03ffff6d8400120 0xfffc1f0380000383 0xf03ffffffa600380

def z1310 : W := mkw 0x141403208824a095 0x67020941b042a366 0x7c7c1f03f8ffe3fc 0xf3933dc1fa63f3e7

def z1311 : W := mkw 0x7242d6fb24919243 0xd83ffff6dfe855a8 0xffffffff801ffff3 0xfd7fffffffe0fff8

def z1312 : W := mkw 0x0001885264900002 0x8838f400070d5000 0x0003ffe3fffe0003 0x8e33fc00067ff000

def z1313 : W := mkw 0x7240000000000001 0x50020bf6d8000000 0xfffc000000000000 0x70132ffff8000000

def z1314 : W := mkw 0x7240000000000000 0x9008fc26d8000000 0x7ffc000000000002 0xf020fe0ff8000000

def z1315 : W := mkw 0x7240000000000001 0x50070bf6d8000000 0xfffc000000000001 0x700f03fff8000000

def z1316 : W := mkw 0x8c9ca364b92ce4bd 0x67020149215aeb77 0x8003ffffffffffff 0x4fff03f007ffffff

def z1317 : W := mkw 0x524256a900019243 0x58376fd2d6e005a8 0xfc7fffff8001fff3 0xfd7f3ff1ffe00ff8

def z1318 : W := mkw 0x000256a900019240 0x0800000006e005a8 0x8003ffff8001fff1 0x0d4c007007e00ff8

def z1319 : W := mkw 0x7240000000000003 0xd03ffd66d8000000 0x7ffc000000000003 0xf03ffdcff8000000

def z1320 : W := mkw 0x0d356d00da656994 0x2f8000092617aec7 0x0003ff007fffff8c 0x0b800000061fff87

def z1321 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003fffff8fffff3 0x4f7f03f007e3fff8

def z1322 : W := mkw 0x7f7467209a65e995 0x77820bfff852afe7 0xfffc00000001fffc 0x718003fff8000fe7

def z1323 : W := mkw 0x0003189244900002 0x0835640006a51000 0x0003ffe3fffe0003 0x8e33fc00067ff000

def z1324 : W := mkw 0x7243188040000003 0xd83ffff6dea50000 0xffffffffffe00003 0xfe3fffffffff0000

def z1325 : W := mkw 0xb09e92f6a5bc84bd 0xe70f9d64b9e8f174 0x800c00ff801e0071 0x144f1c7039e0f078

def z1326 : W := mkw 0x724256a900019243 0x58376bf6dee005a8 0xffffffff8001fff3 0xfd7fe3ffffe00ff8

def z1327 : W := mkw 0x8da96d045b496d28 0x2f80000926178ed7 0x0003ff007fe1fffc 0x0bc00000061f0fff

def z1328 : W := mkw 0x7240000000000001 0x50020bf6d8000000 0xfffc000000000003 0xf00013fff8000000

def z1329 : W := mkw 0x7240000000000001 0xd00afd66d8000000 0x7ffc000000000000 0xb013fd8ff8000000

def z1330 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8ffffc7f1dffff 0xfffcd3fe3f9ccfff

def z1331 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x00001f03fffe0003 0x823ffc00027ff000

def z1332 : W := mkw 0x000398d264900000 0x8808f40007ad5000 0x0003fffffffe0003 0x8e13fc0007fff000

def z1333 : W := mkw 0x724398d264900003 0xd83ffd76dfad5000 0xfffffffffffe0003 0xbe3ffc7ffffff000

def z1334 : W := mkw 0x7240000000000000 0x9008fc26d8000000 0xfffc000000000001 0xb00cfc7ff8000000

def z1335 : W := mkw 0x4d216d005a416902 0x00b0628b40170e83 0x7ff000007fe1ff8e 0xe3b0e38fc01f0f87

def z1336 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3ff007fffff8e 0xebb0ff8fc61fff87

def z1337 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003ffffffffe073 0xcf3ffc4007fff060

def z1338 : W := mkw 0x7240000000000001 0x50020966d8000000 0x7ffc000000000000 0x700001cff8000000

def z1339 : W := mkw 0x7240804020000003 0xd03ffff6d9084000 0xffffe01c07000003 0xf03ffffffd9c0000

def z1340 : W := mkw 0x0000462000018003 0x483203c0064005a0 0x8003ffff8001fff3 0x4d7f03f007e00ff8

def z1341 : W := mkw 0x7240022000008003 0xd03ffff6d8400120 0xfffc00000001e3f3 0xf13ffffff80003e0

def z1342 : W := mkw 0x8c9fbbf6fdbce4bc 0x2f00000927fffb77 0x0003fffffffffffc 0x0fc0000007ffffff

def z1343 : W := mkw 0x7243189244900003 0xd83ffff6dea51000 0xfffc000000000003 0xf03ffffff8000000

def z1344 : W := mkw 0x7240000000000001 0xd00f9ff6d8000000 0xfffc000000000003 0xf02fdffff8000000

def z1345 : W := mkw 0x724256a900019243 0xd83ffff6dee005a8 0x7ffc1f0380000380 0xb013fd8ffa600380

def z1346 : W := mkw 0x0000000000000000 0x0000000000000000 0x8003fffc0001fff3 0x4d7c03f007800ff8

def z1347 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x7c73fffffffe0003 0xee3ffd81c7fff000

def z1348 : W := mkw 0x624398d264900002 0x983df6b64fad5000 0xff8ffffffffe0003 0xfe3ffe7e3ffff000

def z1349 : W := mkw 0x400256a900019243 0x483763d246e005a8 0x8073ffff8001fff3 0x4d7f23f1c7e00ff8

def z1350 : W := mkw 0x000256a900019241 0x4807015006e005a8 0x8003ffff8001fff3 0x4d6f027007e00ff8

def z1351 : W := mkw 0x8dabfdd67fd96d2a 0xafbdf40927bfded7 0x0003ffffffffffff 0x8ffffc0007ffffff

def z1352 : W := mkw 0xbc9c672d992df6fd 0x67020bfdb852afff 0xfffc00000001fffc 0x71c003fff8000fff

def z1353 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3e0007f01ff8e 0xeba0c38fc41c0f87

def z1354 : W := mkw 0x000256a900019241 0x4807015006e005a8 0x8003ffff8001fff3 0x4d5f01f007e00ff8

def z1355 : W := mkw 0x724212a900009243 0xd03ffff6d8e00128 0xfffc000380000003 0xf03ffffff8600000

def z1356 : W := mkw 0x724256a900019241 0xd00f9ff6d8e005a8 0xfffc00ff8001fff1 0x754f1ffff9e00ff8

def z1357 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff3ffe07ffdff8f 0xefb0f38fc61fcf87

def z1358 : W := mkw 0x7240462000018003 0xd83ffff6de4005a0 0xffffffe38001fff3 0xfd3ffffffe600fe0

def z1359 : W := mkw 0x000398d264900002 0x883df69007ad5000 0x8003fffffffe0003 0x8e3ffe3007fff000

def z1360 : W := mkw 0x7240000000000000 0x9008fc26d8000000 0x7ffc1fe3f8fe0003 0xbe13fc0ffa63f000

def z1361 : W := mkw 0x7241081244900000 0x9008fc26d8051000 0x7ffc000000e20000 0xb000fc0ff8033000

def z1362 : W := mkw 0x000256a900019243 0x483703d006e005a8 0x8003ffff8001fff1 0x0d6f027007e00ff8

def z1363 : W := mkw 0x7240000000000000 0x9008fc26d8000000 0x7ffc000000000003 0xf000fc4ff8000000

def z1364 : W := mkw 0x0000804020000000 0x0000000001084000 0x0003fffffffe0003 0x8e133c0007fff000

def z1365 : W := mkw 0x724256a900019243 0xd83ffff6dee005a8 0xffffe01c0001fff0 0x716cc3fffd800ff8

def z1366 : W := mkw 0x724256a900019243 0xd83ffff6dee005a8 0xffffff1f80001f83 0xf07fffffffe00f98

def z1367 : W := mkw 0x7240000000000001 0x50020966d8000000 0x7ffc000000000003 0xf0133dcff8000000

def z1368 : W := mkw 0x0003dcd264910002 0x883df68007ad5480 0x0003fffffffe0383 0x8e3ffd8007fff380

def z1369 : W := mkw 0x7240000000000001 0x50020bf6d8000000 0xfffc000000000003 0x701303fff8000000

def z1370 : W := mkw 0x8da9a9447b486d28 0x27800009211fca57 0x0003e0fc7ffdfc7c 0x0fc00000059fcc7f

def z1371 : W := mkw 0x141403298824b2d5 0x67020951b042a36e 0xfc7c1fe3f8ffe3ff 0xffd33df1fa63f3ff

def z1372 : W := mkw 0x5000000000000003 0x40326bc2d0000000 0x7ffc000000000002 0xf030e3cff8000000

def z1373 : W := mkw 0x7242108000000002 0x983dfc26dea00000 0x7fffffff80000003 0xbc3ffc0fffe00000

def z1374 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xffffe0000001fc03 0xf93ffffffc000c00

def z1375 : W := mkw 0x724398d264900003 0xd83ffff6dfad5000 0xfffffffffffffc73 0xff7ffffffffffc78

def z1376 : W := mkw 0x7243189244900003 0xd83ffff6dea51000 0xffffffff80e20003 0xfc3fffffffe33000

def z1377 : W := mkw 0x0c00210018006000 0x0000000900120a03 0x7ff01f007fe1e38e 0xeb90e18fc21f0387

def z1378 : W := mkw 0x7254022080248097 0xd03ffff6d8402120 0xfffc000380020003 0xf03ffffff8603000

def z1379 : W := mkw 0x7240000000000001 0xd00f9d76d8000000 0xfffc000000000001 0x300f1c7ff8000000

def z1380 : W := mkw 0x100256a900019243 0x48370bd096e005a8 0x8073ffff8001fff3 0x4d7f2ff1c7e00ff8

def z1381 : W := mkw 0x7240000000000002 0x10306aa6d8000000 0x7ffc000000000002 0xf030e38ff8000000

def z1382 : W := mkw 0x7240440900011241 0x50020bf6d8000488 0xfffc000000001c00 0x704003fff8000c18

def z1383 : W := mkw 0x000256a900019242 0x0830028006e005a8 0x8003ffff8001fff3 0x4d7c03f007e00ff8

def z1384 : W := mkw 0x8c88a14439086428 0x27000009211aca57 0x0003fffc7ffdfffc 0x0fc00000079fcfff

def z1385 : W := mkw 0x0003dcdb64911242 0x883df69007ad5488 0x0003fffffffe0003 0x8e3ffc0007fff000

def z1386 : W := mkw 0x724256a900019243 0xd83ffff6dee005a8 0xfffc1f038001fff3 0xf17ffffffa600ff8

def z1387 : W := mkw 0x7241885264900003 0xd83ffff6df0d5000 0xffffff007ffe0003 0xfa3ffffffe1ff000

def z1388 : W := mkw 0x4d2065001a416900 0x0080028b40120e83 0x7ff3e0000701ff8c 0x61a0c38fc41c0f87

def z1389 : W := mkw 0x7242548000010003 0xd83ffff6dea00480 0xffffffff8001ff83 0xfd3fffffffe00f80

def z1390 : W := mkw 0x7240000000000003 0xd03ffff6d8000000 0xfffc00007801e00f 0xfbbffffff8000007

def z1391 : W := mkw 0x400398d264900002 0x883df68247ad5000 0x0383fffffffe0003 0x8e3ffe0e07fff000

def z1392 : W := mkw 0x000212a900009241 0x4007015000e00128 0x8003ffff8001fff3 0x4d7f03f007e00ff8

def z1393 : W := mkw 0x000398d264900002 0x0835640007ad5000 0x0003fffffffe0003 0x8e133c0007fff000

def z1394 : W := mkw 0x7241885264900003 0xd03ffff6d90d5000 0xfffc000007000003 0xf03ffffff81c0000

def z1395 : W := mkw 0xa888a04431084428 0xa708902c2918c855 0xff8fe0fc7f1dfc7c 0x7fecc27e3d9ccc7f

def z1396 : W := mkw 0x101656a9802592d7 0x48370bd096e025a8 0x8003ffff8003fff3 0x4d7f0ff007e03ff8

def z1397 : W := mkw 0x4d237d805a416902 0x08b5628b46b70e83 0x7ff3ffffffffff8f 0xefbfff8fc7ffff87

def z1398 : W := mkw 0x5000000000000002 0x00306a82d0000000 0x7ffc000000000002 0xf030ff8ff8000000

def z1399 : W := mkw 0x00035ebb44919243 0x483767d006e515a8 0x8003ffffffe3fff3 0xcf7feff007ff3ff8

def z1400 : W := mkw 0x7240000000000003 0xd03f9ff6d8000000 0xfffc000000000003 0x703f1ffff8000000

def z1401 : W := mkw 0x4d216d005a416902 0x08b0628b46170e83 0x7ff01f007fe1e38e 0xeb90e18fc21f0387

def z1402 : W := mkw 0x000398d264900002 0x883df40007ad5000 0x0003fffffffffc03 0xcf3ffe0007fffc00

def z1403 : W := mkw 0x000398d264900000 0x800df40001ad5000 0x0003e0fffffe0003 0x8e2ffc0005fff000

def z1404 : W := mkw 0x7240440000010003 0x58320bf6de000480 0xffffff000001ff82 0x793003fffe000f80

def z1405 : W := mkw 0x4d237d925ed16902 0x08b5668b46b71e83 0x7ff3ff007fe1ff8e 0xebb0e38fc61f0f87

def z1406 : W := mkw 0x0001080040000000 0x0000600000050000 0x00001fe3fffe0003 0x8e13fc00027ff000

def z1407 : W := mkw 0x0003dcdb64911242 0x883df69007ad5488 0x8003fffffffffc73 0xcf7ffe7007fffc78

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z8,z4,z5,z6]),(0,[z0,z1,z3,z9,z4,z5,z6]),(0,[z0,z1,z3,z4,z10,z5,z6]),(0,[z0,z1,z11,z3,z4,z12,z6]),(0,[z1,z3,z4,z5,z6,z13,z14])],[(1,[z15,z1,z16,z4,z5,z6]),(0,[z17,z18,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z19,z5,z6]),(0,[z0,z1,z3,z20,z4,z21,z6]),(0,[z22,z0,z1,z3,z4,z5,z6]),(1,[z0,z3,z4,z23,z5,z6]),(0,[z0,z1,z3,z4,z5,z24,z6]),(0,[z0,z1,z25,z3,z4,z5,z6])],[(0,[z26,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z27]),(0,[z28,z0,z1,z3,z4,z5,z6]),(0,[z29,z0,z1,z3,z4,z5,z6]),(0,[z30,z0,z1,z3,z31,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z32]),(0,[z0,z1,z33,z4,z5,z34,z6]),(0,[z0,z1,z35,z3,z4,z5,z36]),(0,[z0,z1,z3,z37,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z38])],[(0,[z39,z0,z1,z3,z4,z5,z6]),(1,[z18,z1,z3,z4,z21,z6]),(0,[z0,z40,z3,z20,z4,z5,z6]),(0,[z0,z41,z3,z4,z5,z6,z42]),(0,[z0,z1,z3,z4,z5,z6,z43]),(0,[z0,z1,z44,z3,z4,z5,z6]),(0,[z0,z1,z45,z3,z4,z5,z46]),(0,[z0,z1,z3,z47,z4,z5,z6])],[(0,[z1,z48,z3,z4,z5,z49,z6]),(0,[z0,z50,z1,z3,z4,z5,z6]),(0,[z15,z0,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z52,z53,z6]),(0,[z0,z1,z3,z54,z4,z5,z6])],[(0,[z1,z3,z4,z51,z5,z21,z6]),(0,[z0,z1,z3,z4,z55,z49,z6]),(0,[z0,z1,z3,z4,z5,z56,z6]),(0,[z0,z1,z3,z4,z55,z12,z6]),(0,[z0,z57,z1,z3,z4,z5,z42]),(0,[z0,z1,z58,z3,z4,z5,z6])],[(0,[z0,z1,z3,z59,z4,z5,z6]),(0,[z0,z1,z3,z60,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z61,z6]),(0,[z0,z1,z3,z4,z5,z6,z62]),(0,[z63,z0,z64,z3,z4,z5,z6]),(0,[z65,z0,z1,z3,z4,z5,z6]),(0,[z66,z0,z1,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z6,z13])]],
   [[(0,[z0,z1,z3,z67,z4,z21,z6]),(0,[z0,z1,z68,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z5,z69,z6]),(0,[z70,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z71,z3,z4,z5,z6]),(0,[z0,z1,z72,z3,z4,z5,z6]),(0,[z0,z1,z33,z3,z67,z4,z6]),(0,[z0,z1,z3,z73,z4,z5,z6])],[(0,[z1,z74,z3,z16,z4,z5,z6]),(0,[z0,z1,z75,z3,z4,z5,z6])],[(1,[z0,z1,z3,z76,z5,z6]),(0,[z0,z40,z48,z3,z4,z5,z6]),(0,[z0,z1,z58,z3,z77,z5,z6]),(0,[z0,z1,z78,z3,z4,z51,z6]),(0,[z0,z79,z1,z3,z4,z5,z6]),(0,[z0,z57,z3,z4,z5,z55,z6]),(0,[z0,z1,z3,z4,z5,z80,z6])],[(1,[z81,z1,z3,z4,z5,z6]),(0,[z30,z65,z0,z3,z4,z5,z6]),(0,[z57,z82,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z83,z6]),(0,[z84,z1,z3,z67,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z85,z6]),(0,[z0,z1,z86,z3,z4,z5,z6]),(0,[z0,z1,z87,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z52,z88,z6])],[(0,[z89,z1,z48,z3,z4,z5,z6]),(1,[z0,z90,z3,z4,z5,z6]),(1,[z91,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z46,z6]),(0,[z0,z1,z45,z3,z5,z6,z14])],[(0,[z0,z1,z3,z4,z5,z6,z92])],[(0,[z0,z93,z1,z3,z4,z5,z6]),(0,[z84,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z67,z5,z94,z6])]],
   [[(0,[z95,z0,z3,z4,z5,z6,z42]),(0,[z0,z1,z3,z4,z5,z96,z6]),(0,[z97,z0,z98,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z52,z5,z6]),(0,[z0,z1,z3,z99,z4,z5,z6])],[(1,[z0,z1,z3,z4,z100,z6]),(0,[z0,z1,z3,z4,z51,z6,z101]),(0,[z89,z0,z1,z3,z4,z5,z6]),(0,[z30,z0,z1,z98,z4,z5,z6]),(0,[z102,z0,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z103,z55,z6]),(0,[z0,z1,z3,z4,z5,z104,z6]),(0,[z105,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z106,z4,z5,z6]),(1,[z63,z1,z3,z77,z5,z6]),(0,[z0,z1,z107,z3,z4,z5,z6]),(1,[z0,z3,z4,z55,z6,z42]),(0,[z108,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z109,z5,z6]),(0,[z0,z1,z3,z4,z5,z110,z6]),(0,[z0,z1,z35,z3,z4,z5,z83]),(0,[z0,z1,z3,z4,z111,z5,z6])],[(0,[z112,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z48,z3,z4,z51,z6]),(0,[z113,z0,z1,z3,z4,z5,z6]),(0,[z114,z0,z1,z3,z4,z5,z6]),(0,[z0,z115,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z67,z4,z51,z6]),(0,[z0,z1,z3,z4,z116,z5,z6]),(0,[z0,z1,z117,z3,z4,z5,z6]),(0,[z0,z1,z118,z3,z4,z5,z6]),(0,[z0,z1,z119,z3,z4,z5,z6]),(0,[z0,z1,z3,z120,z4,z5,z6]),(0,[z0,z1,z3,z121,z4,z52,z6]),(0,[z97,z0,z1,z3,z4,z5,z122]),(0,[z0,z1,z58,z123,z4,z5,z6]),(0,[z0,z1,z124,z3,z4,z5,z6]),(0,[z0,z1,z11,z3,z4,z34,z6]),(0,[z0,z1,z125,z3,z5,z6,z36])],[(0,[z0,z126,z1,z3,z4,z5,z6]),(0,[z0,z127,z1,z3,z4,z5,z6]),(0,[z128,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z77,z52,z6]),(0,[z129,z0,z1,z3,z130,z5,z6]),(0,[z30,z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z131,z20,z5,z6]),(0,[z0,z132,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z133,z6]),(0,[z0,z1,z3,z4,z5,z6,z134]),(0,[z135,z1,z3,z4,z5,z6,z14]),(0,[z0,z1,z3,z4,z5,z6,z14])],[(0,[z0,z1,z136,z3,z4,z5,z6]),(0,[z0,z1,z3,z137,z4,z5,z6]),(0,[z138,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z139,z4,z5,z6])]],
   [[(0,[z0,z0,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z140,z55,z6]),(1,[z0,z141,z3,z4,z5,z6]),(0,[z0,z1,z3,z67,z4,z12,z6])],[(0,[z0,z1,z3,z142,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z143]),(0,[z0,z1,z3,z4,z55,z34,z6])],[(1,[z0,z1,z3,z4,z144,z6]),(0,[z15,z0,z1,z74,z4,z5,z6]),(0,[z145,z0,z1,z3,z4,z5,z6]),(0,[z89,z0,z146,z3,z4,z5,z6]),(0,[z0,z1,z3,z147,z4,z52,z6]),(0,[z0,z1,z148,z3,z4,z5,z6]),(1,[z135,z1,z3,z4,z5,z6])],[(0,[z26,z0,z1,z3,z149,z5,z6]),(0,[z0,z1,z3,z150,z4,z5,z6]),(0,[z22,z0,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z151,z4,z5,z6]),(0,[z0,z1,z3,z152,z4,z5,z6])],[(0,[z26,z0,z1,z3,z4,z51,z6]),(0,[z0,z1,z146,z3,z4,z5,z6]),(0,[z0,z1,z11,z3,z4,z55,z6])],[(0,[z89,z153,z1,z3,z4,z5,z6]),(0,[z154,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z155,z6]),(0,[z0,z1,z3,z4,z5,z156,z6]),(1,[z0,z1,z3,z157,z5,z6]),(0,[z22,z0,z1,z3,z4,z5,z49]),(0,[z0,z40,z1,z3,z20,z5,z6]),(0,[z0,z41,z3,z4,z52,z5,z6]),(0,[z0,z1,z11,z4,z158,z5,z6]),(0,[z0,z141,z1,z3,z4,z5,z6])],[(0,[z153,z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z35,z3,z4,z21,z6]),(0,[z159,z0,z1,z3,z4,z5,z6]),(0,[z91,z57,z1,z3,z4,z5,z6]),(0,[z0,z1,z35,z4,z5,z83,z6])],[(0,[z26,z0,z1,z3,z76,z5,z6]),(0,[z160,z0,z1,z3,z4,z5,z6]),(0,[z0,z161,z1,z3,z4,z5,z6]),(0,[z162,z0,z1,z3,z4,z52,z6]),(0,[z0,z163,z1,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z164,z5,z6]),(0,[z129,z0,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z5,z165,z6]),(0,[z0,z41,z1,z3,z4,z5,z6]),(0,[z0,z1,z166,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z167,z6]),(0,[z97,z0,z1,z3,z4,z168,z6]),(0,[z169,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z170]),(0,[z0,z1,z3,z171,z4,z5,z6])],[(0,[z0,z1,z3,z4,z172,z5,z6]),(0,[z1,z3,z130,z4,z5,z49,z6]),(0,[z65,z0,z1,z3,z4,z51,z6]),(1,[z173,z1,z3,z4,z5,z6]),(0,[z174,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z55,z55,z6]),(0,[z0,z1,z33,z3,z4,z158,z6]),(0,[z175,z0,z1,z3,z4,z5,z6])],[(0,[z63,z0,z1,z3,z4,z164,z6]),(0,[z30,z0,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z176,z4,z5,z6]),(1,[z97,z0,z3,z4,z5,z42]),(1,[z82,z1,z3,z4,z5,z6]),(0,[z0,z1,z58,z4,z103,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z177])],[(0,[z129,z0,z1,z3,z4,z178,z6]),(0,[z162,z1,z3,z4,z5,z49,z6]),(0,[z179,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z180,z3,z4,z5,z6]),(0,[z181,z0,z1,z3,z4,z5,z6])],[(0,[z182,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z20,z130,z5,z6]),(0,[z0,z1,z3,z4,z183,z5,z6]),(0,[z0,z1,z123,z131,z4,z5,z6])],[(0,[z0,z57,z48,z3,z4,z5,z6]),(0,[z0,z1,z3,z16,z4,z5,z6]),(0,[z0,z1,z3,z4,z51,z122,z6]),(0,[z0,z1,z3,z4,z184,z5,z6]),(0,[z0,z1,z3,z4,z185,z5,z6])],[(0,[z26,z0,z1,z3,z4,z100,z6]),(0,[z0,z1,z3,z4,z5,z178,z6]),(0,[z186,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z187,z3,z4,z5,z6]),(0,[z0,z1,z3,z188,z4,z21,z6]),(0,[z0,z1,z3,z4,z5,z189,z6])],[(0,[z0,z40,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z23,z5,z6])]],
   [[(0,[z0,z1,z74,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z103,z21,z6]),(0,[z0,z1,z3,z4,z21,z6,z14]),(0,[z0,z1,z3,z190,z4,z5,z6]),(1,[z0,z1,z3,z191,z5,z6])],[(0,[z95,z1,z48,z3,z4,z5,z6]),(0,[z15,z0,z1,z3,z4,z192,z6]),(0,[z0,z193,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z194]),(0,[z0,z1,z3,z195,z4,z5,z6]),(0,[z0,z1,z3,z196,z5,z46,z6]),(0,[z0,z1,z197,z3,z4,z5,z6])],[(0,[z153,z0,z1,z3,z4,z51,z6]),(1,[z0,z1,z3,z31,z5,z6]),(1,[z198,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z20,z5,z46,z6]),(0,[z0,z1,z199,z3,z4,z52,z6]),(1,[z0,z1,z3,z4,z200,z6])],[(0,[z0,z1,z3,z4,z5,z6,z201]),(0,[z89,z0,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z202,z4,z55,z6]),(0,[z0,z1,z3,z203,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z204,z6])],[(1,[z0,z1,z3,z4,z192,z6]),(0,[z0,z1,z74,z3,z4,z52,z6]),(0,[z30,z0,z1,z3,z205,z5,z6]),(0,[z206,z0,z1,z3,z4,z5,z6]),(0,[z207,z0,z1,z3,z4,z5,z6])],[(0,[z95,z0,z1,z3,z4,z5,z6]),(0,[z208,z0,z1,z3,z4,z5,z6]),(0,[z89,z0,z1,z3,z4,z5,z49]),(0,[z209,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z210,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z55,z94,z6]),(0,[z0,z1,z3,z196,z4,z52,z6]),(0,[z0,z1,z3,z188,z5,z94,z6]),(0,[z0,z1,z199,z3,z188,z5,z6])],[(0,[z63,z0,z211,z3,z4,z5,z6]),(0,[z112,z0,z1,z3,z4,z51,z6]),(0,[z113,z0,z1,z3,z4,z51,z6]),(0,[z0,z115,z1,z3,z4,z51,z6])],[(0,[z0,z1,z3,z212,z4,z5,z6]),(0,[z0,z1,z3,z4,z140,z21,z6]),(0,[z213,z0,z1,z3,z4,z5,z6]),(0,[z0,z40,z1,z3,z4,z214,z6]),(0,[z0,z1,z215,z3,z4,z5,z6]),(0,[z216,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z217])]],
   [[(0,[z0,z1,z218,z3,z4,z103,z6]),(0,[z0,z1,z219,z3,z4,z5,z6])],[(0,[z153,z95,z1,z3,z4,z5,z6]),(0,[z95,z0,z1,z3,z4,z52,z6]),(0,[z89,z63,z1,z3,z4,z5,z6]),(0,[z63,z0,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z5,z220,z6]),(0,[z0,z1,z3,z4,z12,z6,z221])],[(0,[z63,z0,z1,z3,z77,z5,z6]),(0,[z222,z0,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z188,z4,z51,z6]),(0,[z0,z1,z3,z223,z4,z5,z6]),(0,[z0,z1,z224,z3,z4,z5,z6]),(0,[z0,z225,z1,z98,z4,z5,z6]),(0,[z0,z40,z3,z4,z5,z55,z6])],[(0,[z0,z1,z90,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z21,z6,z36]),(0,[z0,z1,z226,z3,z4,z5,z6]),(0,[z30,z97,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z168,z5,z6]),(0,[z227,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z48,z3,z4,z55,z6]),(0,[z228,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z229,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z51,z21,z6]),(0,[z0,z1,z3,z4,z230,z5,z6]),(0,[z231,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z232,z6]),(0,[z0,z1,z3,z67,z4,z55,z6]),(0,[z0,z233,z1,z3,z4,z5,z6])],[(0,[z63,z1,z3,z4,z5,z49,z6]),(0,[z0,z1,z3,z4,z234,z5,z6]),(1,[z0,z3,z4,z140,z55,z6]),(0,[z0,z1,z3,z235,z4,z5,z6])],[(0,[z18,z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z33,z3,z4,z21,z6]),(1,[z89,z1,z3,z4,z5,z101]),(0,[z0,z98,z3,z4,z5,z122,z6]),(0,[z236,z0,z3,z4,z5,z6,z36]),(0,[z0,z1,z237,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z238]),(0,[z153,z1,z3,z16,z4,z5,z6]),(0,[z0,z225,z1,z3,z4,z21,z6]),(0,[z239,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z240,z6]),(0,[z0,z241,z1,z3,z4,z5,z6]),(0,[z242,z0,z1,z3,z4,z5,z6]),(0,[z243,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z244,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z245,z5,z6]),(0,[z0,z1,z35,z16,z4,z5,z6]),(0,[z0,z1,z3,z4,z55,z6,z42]),(0,[z0,z1,z3,z4,z158,z5,z6]),(0,[z0,z1,z3,z4,z5,z246,z6]),(0,[z0,z1,z3,z4,z5,z247,z6]),(0,[z0,z1,z248,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z249,z5,z6]),(0,[z0,z1,z3,z4,z250,z5,z6]),(1,[z0,z1,z3,z251,z5,z6]),(0,[z252,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z253,z4,z5,z6]),(0,[z254,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z55,z255,z6]),(0,[z256,z0,z1,z3,z4,z5,z6])],[(0,[z18,z0,z1,z3,z4,z257,z6]),(1,[z1,z72,z3,z4,z5,z6]),(0,[z243,z0,z1,z3,z4,z5,z83])],[(0,[z95,z0,z3,z4,z140,z5,z6]),(0,[z15,z0,z1,z3,z4,z21,z6]),(0,[z89,z1,z74,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z258,z5,z6]),(0,[z22,z0,z1,z3,z4,z55,z6]),(1,[z0,z1,z3,z4,z259,z6]),(0,[z260,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z261,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z262,z6]),(0,[z0,z1,z3,z4,z5,z6,z221])],[(0,[z0,z1,z3,z4,z5,z263,z6]),(0,[z0,z1,z3,z4,z5,z6,z264]),(0,[z97,z0,z3,z4,z5,z6,z42]),(0,[z0,z1,z265,z3,z4,z5,z6])],[(0,[z266,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z267,z3,z4,z5,z6]),(0,[z0,z1,z268,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z21,z6]),(0,[z269,z0,z1,z3,z4,z5,z6]),(0,[z0,z57,z1,z3,z4,z5,z6])],[(0,[z270,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z271,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z272,z6]),(0,[z0,z1,z3,z4,z5,z6,z273]),(1,[z0,z3,z4,z5,z6,z177])]],
   [[(0,[z0,z1,z3,z4,z51,z51,z6]),(0,[z22,z0,z1,z3,z4,z274,z6]),(0,[z0,z1,z3,z4,z5,z6,z275]),(0,[z0,z1,z123,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z276,z52,z6]),(0,[z0,z1,z3,z67,z4,z94,z6]),(0,[z0,z1,z3,z4,z5,z6,z277])],[(0,[z278,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z123,z3,z77,z5,z6]),(0,[z65,z0,z1,z3,z4,z55,z6]),(0,[z0,z1,z45,z3,z20,z5,z6]),(0,[z0,z1,z267,z3,z4,z52,z6]),(0,[z0,z1,z279,z3,z4,z5,z6]),(0,[z0,z1,z199,z3,z202,z4,z6])],[(0,[z18,z0,z1,z3,z4,z51,z6]),(0,[z30,z0,z1,z3,z4,z55,z6]),(0,[z0,z98,z3,z20,z4,z5,z6]),(0,[z0,z280,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z281,z4,z5,z6]),(0,[z0,z141,z3,z4,z158,z5,z6])],[(0,[z282,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z283,z3,z4,z5,z6]),(0,[z0,z225,z1,z3,z4,z51,z6]),(0,[z0,z1,z284,z3,z4,z5,z6]),(0,[z0,z1,z3,z271,z4,z52,z6]),(0,[z0,z1,z58,z3,z131,z5,z6]),(0,[z0,z1,z125,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z285,z5,z6]),(0,[z0,z1,z3,z4,z51,z49,z6]),(0,[z0,z1,z3,z4,z51,z12,z6]),(0,[z0,z1,z3,z286,z4,z5,z6]),(0,[z65,z198,z1,z3,z4,z5,z6]),(0,[z0,z1,z58,z45,z3,z5,z6]),(0,[z0,z1,z218,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z287,z5,z6])],[(0,[z0,z1,z288,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z289,z6]),(0,[z0,z1,z131,z4,z103,z5,z6]),(0,[z0,z1,z3,z4,z5,z290,z6]),(0,[z0,z1,z3,z4,z5,z6,z291])],[(1,[z0,z1,z3,z4,z292,z6]),(0,[z0,z1,z16,z4,z5,z6,z36]),(0,[z0,z1,z3,z4,z293,z55,z6]),(0,[z0,z1,z33,z3,z4,z12,z6]),(0,[z0,z1,z3,z4,z5,z6,z294])],[(0,[z0,z1,z68,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z295]),(0,[z0,z1,z3,z4,z296,z5,z6]),(0,[z0,z1,z3,z297,z4,z5,z6]),(0,[z0,z1,z3,z298,z4,z6,z36]),(0,[z0,z1,z3,z299,z4,z5,z6])]],
   [[(0,[z18,z0,z90,z3,z4,z5,z6]),(0,[z300,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z98,z3,z4,z52,z6]),(0,[z0,z1,z3,z301,z4,z5,z6]),(0,[z0,z1,z302,z3,z4,z5,z6]),(0,[z0,z1,z303,z3,z4,z5,z6]),(0,[z0,z304,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z149,z5,z6]),(0,[z305,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z306]),(1,[z129,z1,z3,z4,z21,z6])],[(0,[z153,z0,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z5,z307,z6]),(1,[z0,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z308,z21,z6]),(0,[z0,z309,z1,z3,z4,z5,z6]),(0,[z0,z1,z35,z3,z4,z55,z6]),(1,[z0,z1,z3,z5,z6,z310]),(1,[z0,z1,z3,z4,z311,z6])],[(0,[z0,z1,z48,z3,z4,z21,z6]),(0,[z89,z0,z1,z3,z4,z55,z6]),(0,[z0,z1,z45,z3,z4,z52,z6]),(1,[z0,z1,z33,z4,z34,z6])],[(0,[z0,z1,z3,z31,z4,z5,z6]),(0,[z312,z0,z1,z3,z4,z5,z6]),(0,[z313,z0,z1,z3,z4,z5,z6])],[(0,[z314,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z21,z6,z221]),(0,[z0,z1,z3,z4,z5,z6,z101]),(0,[z0,z1,z3,z315,z4,z5,z6]),(0,[z0,z1,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z55,z83,z6]),(0,[z316,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z311,z6,z14]),(0,[z317,z1,z3,z4,z318,z5,z6])],[(1,[z0,z1,z3,z4,z319,z6]),(0,[z0,z1,z3,z320,z4,z5,z6]),(0,[z30,z0,z3,z147,z4,z5,z6]),(0,[z0,z1,z3,z4,z259,z5,z6]),(0,[z0,z1,z321,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z55,z85,z6]),(0,[z112,z0,z1,z3,z4,z55,z6]),(0,[z0,z1,z118,z3,z4,z55,z6]),(0,[z0,z3,z4,z5,z122,z6,z42]),(0,[z322,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z323,z3,z4,z5,z6]),(0,[z0,z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z324,z5,z6]),(0,[z0,z1,z325,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z55,z46,z6]),(1,[z236,z0,z3,z4,z5,z6]),(0,[z0,z1,z326,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z327,z3,z4,z5,z6]),(0,[z0,z64,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z4,z5,z6]),(0,[z89,z1,z3,z130,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z328,z6]),(0,[z0,z1,z3,z4,z52,z329,z6])],[(0,[z0,z1,z330,z3,z4,z5,z6]),(0,[z243,z0,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z331,z5,z6]),(0,[z0,z1,z3,z332,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z333]),(0,[z0,z1,z199,z3,z67,z5,z6])],[(0,[z0,z1,z334,z3,z4,z5,z6]),(0,[z18,z0,z1,z3,z335,z5,z6]),(0,[z18,z1,z74,z3,z4,z5,z6]),(0,[z22,z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z158,z51,z6]),(0,[z0,z1,z3,z336,z4,z5,z6]),(0,[z337,z0,z1,z3,z4,z5,z6]),(1,[z30,z0,z147,z4,z5,z6]),(0,[z65,z0,z1,z3,z140,z5,z6]),(0,[z0,z1,z3,z188,z4,z55,z6]),(0,[z0,z1,z3,z4,z52,z122,z6])],[(0,[z26,z0,z1,z3,z4,z21,z6]),(0,[z29,z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z249,z51,z6]),(0,[z0,z1,z3,z121,z4,z5,z6]),(0,[z0,z1,z3,z4,z338,z5,z6])],[(0,[z30,z95,z0,z3,z4,z5,z6]),(0,[z15,z1,z3,z16,z4,z5,z6]),(1,[z0,z1,z3,z205,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z339])],[(0,[z15,z0,z1,z16,z4,z5,z6]),(0,[z340,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z77,z5,z6]),(1,[z0,z1,z3,z4,z341,z6]),(0,[z65,z0,z1,z3,z4,z259,z6]),(0,[z102,z0,z1,z3,z4,z52,z6])],[(0,[z0,z1,z3,z342,z4,z5,z6]),(0,[z0,z1,z58,z3,z4,z21,z6]),(0,[z30,z0,z3,z4,z5,z122,z6]),(0,[z0,z1,z3,z343,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z53,z6]),(0,[z0,z1,z3,z4,z52,z94,z6]),(1,[z0,z1,z45,z3,z5,z14])],[(0,[z0,z1,z344,z3,z4,z5,z6]),(0,[z129,z1,z3,z4,z5,z21,z6]),(0,[z0,z1,z3,z130,z4,z51,z6]),(0,[z345,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z58,z103,z5,z6]),(0,[z0,z1,z3,z346,z4,z5,z6]),(1,[z0,z1,z3,z202,z4,z221]),(0,[z0,z1,z347,z3,z4,z5,z6])]],
   [[(0,[z18,z0,z1,z74,z4,z5,z6]),(0,[z0,z1,z74,z35,z4,z5,z6]),(0,[z65,z0,z1,z3,z4,z21,z6]),(0,[z0,z57,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z5,z348,z6]),(0,[z0,z1,z3,z4,z51,z34,z6])],[(0,[z0,z1,z3,z147,z4,z5,z6]),(0,[z0,z1,z349,z3,z4,z5,z6]),(0,[z0,z1,z3,z350,z4,z5,z6]),(0,[z351,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z352,z3,z4,z5,z6]),(1,[z0,z1,z3,z335,z5,z6]),(0,[z129,z162,z1,z3,z4,z5,z6]),(0,[z102,z0,z41,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z353,z5,z6]),(0,[z0,z1,z33,z3,z4,z34,z6])],[(0,[z129,z1,z48,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z354,z5,z6]),(0,[z0,z1,z3,z355,z4,z5,z6]),(1,[z0,z1,z3,z4,z356,z6]),(0,[z0,z1,z357,z3,z4,z5,z6]),(0,[z0,z1,z3,z358,z4,z5,z6])],[(0,[z153,z95,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z51,z359,z6]),(0,[z360,z0,z1,z3,z4,z55,z6]),(0,[z0,z1,z4,z158,z5,z34,z6]),(0,[z0,z1,z3,z4,z361,z5,z6])],[(0,[z89,z0,z1,z3,z251,z5,z6]),(0,[z173,z0,z1,z3,z4,z5,z6]),(0,[z362,z0,z1,z3,z4,z5,z6]),(0,[z97,z0,z1,z3,z4,z52,z6])],[(0,[z0,z1,z363,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z364,z6]),(0,[z162,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z365,z5,z6]),(1,[z0,z1,z3,z4,z366,z6]),(0,[z0,z1,z3,z4,z5,z88,z6]),(0,[z367,z1,z3,z4,z5,z6,z36]),(1,[z0,z1,z3,z67,z94,z6])],[(0,[z129,z0,z1,z3,z4,z5,z6]),(0,[z368,z0,z1,z3,z4,z5,z6]),(0,[z369,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z21,z6,z101]),(0,[z0,z1,z3,z131,z4,z5,z6]),(0,[z0,z1,z3,z4,z318,z5,z6])]],
   [[(0,[z1,z3,z4,z77,z5,z21,z6]),(0,[z0,z1,z3,z4,z51,z55,z6]),(0,[z89,z1,z3,z4,z5,z6,z101]),(1,[z0,z1,z3,z4,z183,z6]),(0,[z102,z0,z3,z4,z5,z55,z6]),(1,[z0,z1,z3,z4,z293,z6]),(0,[z0,z1,z11,z3,z4,z52,z6])],[(0,[z370,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z48,z3,z4,z85,z6]),(0,[z0,z1,z3,z4,z52,z21,z6]),(0,[z0,z1,z3,z4,z52,z6,z42]),(0,[z0,z1,z371,z3,z4,z5,z6])],[(0,[z18,z0,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z5,z5,z6]),(0,[z89,z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z58,z3,z4,z51,z6]),(0,[z22,z0,z1,z3,z4,z5,z101]),(0,[z30,z0,z3,z20,z4,z5,z6]),(0,[z0,z1,z33,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z5,z372,z6])],[(0,[z26,z0,z1,z3,z4,z319,z6]),(0,[z0,z225,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z131,z4,z52,z6]),(0,[z0,z1,z3,z4,z318,z52,z6]),(0,[z97,z0,z1,z3,z4,z5,z42]),(0,[z0,z1,z3,z4,z373,z5,z6])],[(0,[z1,z74,z3,z4,z5,z49,z6]),(0,[z129,z0,z1,z3,z77,z5,z6]),(0,[z30,z0,z1,z147,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z36])],[(0,[z0,z1,z3,z4,z5,z374,z6]),(0,[z112,z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z5,z6,z375])],[(0,[z1,z48,z3,z16,z4,z5,z6]),(0,[z376,z0,z1,z3,z4,z5,z6]),(0,[z18,z0,z1,z3,z4,z19,z6]),(1,[z1,z3,z4,z51,z21,z6]),(1,[z0,z1,z3,z4,z359,z6]),(0,[z0,z40,z1,z3,z4,z5,z6]),(0,[z377,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z378,z5,z6]),(0,[z0,z1,z3,z4,z379,z5,z6]),(0,[z0,z380,z1,z3,z4,z5,z6])],[(0,[z153,z1,z3,z4,z77,z5,z6]),(0,[z15,z0,z1,z3,z4,z55,z6]),(0,[z0,z3,z20,z4,z140,z5,z6]),(1,[z0,z3,z4,z52,z55,z6]),(0,[z243,z0,z1,z35,z4,z5,z6])]],
   [[(0,[z0,z48,z98,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z341,z5,z6]),(0,[z30,z0,z1,z3,z4,z56,z6]),(0,[z97,z0,z1,z3,z4,z381,z6]),(0,[z0,z1,z199,z3,z188,z4,z6])],[(0,[z0,z1,z382,z3,z4,z5,z6]),(0,[z222,z1,z3,z4,z5,z21,z6]),(0,[z383,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z199,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z55,z6]),(0,[z0,z1,z4,z5,z83,z6,z36])],[(0,[z0,z1,z384,z3,z4,z5,z6]),(0,[z0,z1,z385,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z386,z6]),(0,[z0,z1,z3,z4,z5,z6,z387]),(0,[z65,z0,z40,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z388,z5,z6])],[(0,[z222,z162,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z51,z94,z6]),(0,[z243,z0,z1,z3,z4,z5,z36]),(0,[z0,z1,z3,z196,z4,z5,z6]),(0,[z0,z1,z3,z389,z4,z5,z6])],[(0,[z0,z1,z3,z4,z76,z5,z6]),(0,[z390,z0,z1,z3,z4,z55,z6])],[(1,[z0,z1,z3,z4,z19,z6]),(0,[z391,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z214,z6])],[(0,[z0,z1,z3,z4,z77,z51,z6]),(0,[z0,z1,z3,z392,z4,z5,z6]),(1,[z0,z1,z3,z4,z274,z6]),(0,[z393,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z202,z4,z52,z6]),(0,[z0,z1,z3,z394,z4,z5,z6]),(0,[z0,z1,z395,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z396])]],
   [[(0,[z63,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z397,z5,z6]),(0,[z0,z1,z3,z4,z5,z398,z6]),(0,[z0,z1,z3,z4,z5,z399,z6]),(0,[z0,z1,z400,z3,z4,z5,z6]),(0,[z0,z1,z401,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z402]),(0,[z0,z1,z199,z33,z3,z4,z6]),(0,[z0,z1,z403,z3,z4,z5,z6]),(0,[z404,z0,z1,z3,z4,z5,z6]),(0,[z405,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z406,z6])],[(0,[z407,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z196,z77,z5,z6]),(0,[z0,z1,z3,z408,z4,z5,z6]),(0,[z222,z0,z1,z3,z4,z5,z6]),(0,[z0,z41,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z409,z4,z5,z6]),(0,[z0,z1,z3,z4,z52,z49,z6]),(0,[z0,z1,z3,z4,z5,z6,z410]),(0,[z0,z98,z3,z4,z5,z55,z6]),(0,[z0,z1,z3,z20,z4,z52,z6]),(0,[z243,z0,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z52,z12,z6]),(0,[z0,z1,z3,z4,z5,z381,z6]),(1,[z0,z1,z3,z4,z168,z6]),(0,[z0,z411,z3,z67,z4,z5,z6])],[(0,[z0,z1,z3,z20,z77,z5,z6]),(0,[z89,z0,z1,z3,z4,z5,z101]),(0,[z0,z1,z3,z4,z158,z55,z6]),(0,[z0,z1,z3,z4,z5,z412,z6])],[(0,[z0,z1,z3,z4,z21,z122,z6]),(0,[z0,z1,z3,z147,z4,z51,z6]),(0,[z0,z413,z1,z3,z4,z5,z6])],[(0,[z0,z1,z48,z3,z4,z249,z6]),(0,[z0,z1,z3,z4,z5,z257,z6]),(0,[z89,z0,z1,z414,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z415,z6]),(0,[z0,z1,z3,z4,z5,z6,z416]),(1,[z0,z41,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z5,z417,z6]),(0,[z0,z1,z3,z4,z5,z418,z6]),(1,[z0,z3,z346,z4,z5,z6])],[(0,[z0,z1,z3,z4,z419,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z420]),(0,[z22,z0,z1,z3,z4,z324,z6])],[(0,[z0,z1,z3,z16,z4,z21,z6]),(0,[z0,z1,z3,z4,z5,z6,z421]),(0,[z0,z1,z3,z4,z422,z103,z6]),(1,[z0,z1,z3,z4,z423,z6]),(0,[z0,z424,z1,z3,z4,z5,z6])],[(0,[z89,z15,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z130,z4,z55,z6]),(0,[z0,z1,z187,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z51,z6,z42]),(0,[z1,z3,z4,z5,z49,z6,z101]),(0,[z0,z1,z3,z4,z425,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z426]),(0,[z0,z1,z11,z3,z202,z4,z6])]],
   [[(0,[z162,z0,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z150,z4,z51,z6]),(0,[z0,z1,z427,z3,z4,z5,z6]),(0,[z89,z0,z428,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z429]),(0,[z0,z1,z430,z3,z4,z5,z6]),(0,[z65,z0,z1,z3,z4,z366,z6]),(0,[z0,z57,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z67,z4,z52,z6]),(0,[z0,z1,z3,z4,z5,z431,z6]),(0,[z0,z1,z3,z4,z5,z6,z432])],[(0,[z0,z1,z74,z3,z4,z21,z6]),(0,[z0,z1,z433,z3,z4,z5,z6]),(0,[z0,z57,z1,z3,z191,z5,z6])],[(1,[z0,z1,z3,z4,z434,z6]),(0,[z0,z1,z123,z3,z131,z5,z6])],[(0,[z0,z1,z3,z149,z4,z5,z6]),(0,[z63,z129,z1,z3,z4,z5,z6]),(0,[z65,z0,z98,z3,z4,z5,z6]),(0,[z0,z57,z1,z3,z4,z200,z6]),(0,[z435,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z436,z6]),(0,[z0,z1,z45,z123,z3,z5,z6])],[(0,[z0,z41,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z10,z55,z6]),(1,[z0,z411,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z437])],[(0,[z0,z1,z3,z4,z21,z438,z6]),(1,[z65,z0,z3,z140,z5,z6])],[(0,[z26,z0,z1,z3,z4,z55,z6]),(0,[z30,z0,z1,z3,z4,z5,z439]),(0,[z0,z1,z3,z4,z276,z5,z6]),(0,[z0,z1,z123,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z440,z5,z6])]],
   [[(0,[z0,z40,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z157,z5,z6]),(0,[z0,z1,z441,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z442,z6])],[(0,[z443,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z444,z3,z4,z5,z6])],[(0,[z445,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z16,z4,z51,z6]),(0,[z0,z1,z58,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z200,z5,z6]),(0,[z446,z0,z1,z3,z4,z5,z6])],[(0,[z15,z0,z1,z3,z4,z447,z6]),(0,[z448,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z199,z3,z4,z51,z6]),(0,[z0,z1,z3,z60,z4,z55,z6]),(0,[z0,z1,z449,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z450,z5,z6]),(1,[z0,z64,z3,z4,z5,z6]),(1,[z169,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z451,z6])],[(0,[z0,z1,z3,z452,z4,z5,z6]),(0,[z0,z1,z74,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z52,z34,z6]),(0,[z0,z1,z3,z4,z5,z453,z6]),(0,[z0,z1,z3,z202,z4,z318,z6])],[(0,[z0,z1,z3,z4,z5,z100,z6]),(0,[z95,z0,z1,z3,z4,z292,z6]),(0,[z162,z1,z3,z4,z51,z5,z6]),(0,[z0,z1,z3,z196,z4,z51,z6]),(0,[z30,z0,z1,z3,z4,z52,z6]),(0,[z454,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z455,z5,z6]),(0,[z0,z3,z4,z23,z103,z5,z6]),(0,[z0,z1,z456,z3,z4,z5,z6]),(0,[z0,z1,z457,z3,z4,z5,z6]),(0,[z0,z458,z3,z202,z4,z5,z6])],[(0,[z0,z1,z3,z4,z447,z5,z6]),(0,[z0,z1,z98,z3,z4,z5,z6]),(0,[z459,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z202,z4,z6,z221])]],
   [[(0,[z460,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z130,z140,z5,z6]),(0,[z243,z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z5,z461,z6]),(0,[z0,z1,z11,z33,z4,z5,z6]),(0,[z0,z1,z3,z298,z4,z5,z6]),(1,[z1,z3,z462,z4,z5,z6])],[(0,[z0,z1,z3,z4,z158,z21,z6])],[(0,[z95,z0,z1,z3,z4,z51,z6]),(0,[z63,z0,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z140,z103,z5,z6]),(0,[z0,z1,z3,z4,z422,z5,z6]),(0,[z0,z411,z1,z3,z4,z5,z6]),(0,[z0,z1,z45,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z463,z6])],[(0,[z0,z1,z3,z4,z464,z5,z6]),(0,[z465,z0,z1,z3,z4,z5,z6]),(1,[z17,z0,z3,z4,z5,z6]),(0,[z0,z1,z466,z3,z4,z5,z6]),(0,[z30,z0,z41,z3,z4,z5,z6]),(0,[z0,z1,z3,z332,z4,z55,z6]),(0,[z0,z1,z3,z4,z191,z5,z6]),(0,[z0,z1,z11,z199,z3,z4,z6])],[(0,[z0,z1,z3,z4,z5,z6,z467]),(0,[z0,z1,z3,z4,z258,z21,z6]),(0,[z0,z1,z3,z4,z21,z6,z468]),(0,[z0,z1,z3,z4,z51,z83,z6]),(0,[z198,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z58,z3,z103,z5,z6])],[(0,[z0,z1,z3,z4,z469,z5,z6]),(0,[z0,z1,z3,z470,z4,z5,z6]),(0,[z0,z1,z3,z4,z52,z55,z6])],[(0,[z153,z0,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z130,z4,z21,z6]),(0,[z0,z1,z3,z4,z51,z46,z6]),(0,[z0,z1,z3,z4,z471,z5,z6]),(0,[z0,z1,z35,z3,z4,z52,z6])],[(0,[z0,z1,z3,z4,z5,z144,z6]),(0,[z0,z57,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z472,z5,z6]),(0,[z0,z1,z3,z4,z372,z6,z36]),(0,[z0,z1,z3,z4,z5,z6,z473]),(0,[z0,z1,z3,z4,z318,z5,z12])]],
   [[(1,[z0,z1,z3,z4,z419,z6]),(1,[z0,z1,z3,z4,z56,z6]),(0,[z474,z0,z1,z3,z4,z5,z6])],[(0,[z95,z0,z40,z3,z4,z5,z6]),(0,[z0,z1,z3,z475,z4,z5,z6]),(0,[z30,z0,z3,z4,z5,z55,z6]),(0,[z0,z1,z3,z476,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z477,z6])],[(0,[z153,z18,z1,z3,z4,z5,z6]),(0,[z153,z1,z3,z4,z5,z49,z6]),(0,[z0,z1,z3,z4,z5,z478,z6]),(0,[z0,z1,z3,z4,z21,z49,z6]),(0,[z0,z1,z3,z4,z21,z12,z6]),(0,[z30,z0,z225,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z479,z5,z6]),(0,[z0,z1,z3,z5,z46,z6,z14])],[(0,[z18,z0,z1,z16,z4,z5,z6]),(0,[z0,z1,z3,z480,z4,z5,z6]),(1,[z0,z1,z414,z4,z5,z6]),(1,[z0,z1,z3,z4,z481,z6]),(0,[z0,z1,z3,z4,z55,z6,z333]),(0,[z0,z1,z3,z4,z5,z482,z6]),(0,[z383,z1,z33,z3,z4,z5,z6])],[(0,[z483,z0,z1,z3,z4,z5,z6]),(0,[z0,z48,z3,z4,z5,z6,z42]),(0,[z0,z1,z484,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z485,z6]),(0,[z0,z1,z486,z3,z4,z5,z6]),(0,[z0,z41,z98,z3,z4,z5,z6]),(0,[z102,z0,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z42,z36]),(0,[z0,z1,z3,z4,z5,z6,z487])],[(0,[z1,z48,z3,z4,z77,z5,z6]),(0,[z0,z1,z3,z488,z4,z5,z6]),(0,[z0,z1,z3,z489,z4,z5,z6]),(0,[z0,z1,z3,z188,z4,z52,z6]),(0,[z0,z1,z3,z196,z4,z5,z14])],[(1,[z0,z1,z3,z4,z85,z6]),(0,[z0,z1,z490,z3,z4,z5,z6]),(0,[z89,z22,z1,z3,z4,z5,z6]),(1,[z0,z428,z3,z4,z5,z6]),(1,[z1,z3,z4,z5,z6,z375])]],
   [[(0,[z491,z0,z1,z3,z4,z5,z6]),(0,[z492,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z493,z6]),(0,[z0,z1,z3,z4,z5,z359,z6]),(0,[z0,z1,z3,z4,z103,z52,z6])],[(0,[z0,z1,z123,z3,z4,z51,z6]),(0,[z0,z1,z3,z462,z4,z5,z6]),(0,[z0,z1,z3,z4,z311,z5,z6])],[(0,[z0,z3,z4,z52,z5,z55,z6]),(0,[z0,z1,z494,z3,z4,z52,z6]),(1,[z0,z1,z125,z3,z5,z6])],[(0,[z0,z1,z3,z4,z55,z6,z14]),(0,[z0,z1,z3,z495,z4,z5,z6])],[(0,[z0,z1,z3,z496,z4,z5,z6]),(0,[z97,z0,z1,z3,z4,z5,z6]),(1,[z367,z1,z3,z4,z5,z6]),(0,[z0,z1,z497,z3,z4,z5,z6]),(1,[z317,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z498]),(0,[z0,z225,z98,z3,z4,z5,z6]),(0,[z0,z41,z1,z3,z4,z55,z6])],[(0,[z129,z1,z3,z130,z4,z5,z6]),(0,[z0,z1,z3,z4,z51,z156,z6]),(0,[z30,z0,z1,z3,z4,z5,z499]),(0,[z0,z1,z3,z4,z500,z5,z6]),(0,[z0,z3,z67,z501,z4,z5,z6]),(0,[z0,z502,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z503,z5,z6])],[(0,[z504,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z505,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z140,z52,z6]),(0,[z0,z1,z3,z176,z4,z55,z6]),(0,[z0,z1,z11,z3,z4,z5,z6]),(0,[z0,z1,z3,z506,z4,z5,z6])]],
   [[(0,[z507,z0,z1,z3,z4,z5,z6]),(0,[z0,z40,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z508,z5,z6])],[(0,[z0,z1,z3,z4,z5,z192,z6]),(0,[z0,z1,z98,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z5,z6,z509]),(0,[z0,z1,z3,z4,z510,z5,z6]),(1,[z0,z458,z3,z4,z5,z6])],[(0,[z0,z1,z3,z16,z4,z55,z6]),(0,[z0,z1,z330,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z5,z6,z511]),(0,[z0,z1,z3,z4,z5,z329,z6]),(0,[z0,z1,z3,z4,z512,z5,z6]),(0,[z0,z1,z3,z4,z5,z513,z6])],[(0,[z0,z1,z3,z4,z514,z5,z6]),(0,[z0,z1,z199,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z515,z5,z6])],[(0,[z0,z1,z3,z516,z4,z5,z6]),(0,[z0,z1,z45,z3,z4,z51,z6]),(1,[z0,z1,z3,z4,z324,z6]),(0,[z0,z1,z3,z4,z5,z122,z6]),(0,[z0,z1,z3,z517,z4,z5,z6])],[(0,[z0,z1,z74,z3,z4,z55,z6]),(0,[z0,z518,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z519,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z520,z6])],[(0,[z18,z0,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z77,z21,z6]),(0,[z0,z1,z3,z4,z21,z34,z6]),(0,[z0,z1,z3,z4,z5,z6,z439]),(0,[z0,z1,z3,z521,z4,z5,z6]),(0,[z0,z1,z3,z4,z55,z6,z36]),(0,[z0,z1,z33,z3,z4,z52,z6])],[(0,[z1,z3,z4,z5,z21,z49,z6]),(1,[z0,z1,z3,z4,z5,z439]),(1,[z0,z1,z3,z394,z5,z6]),(1,[z243,z0,z1,z4,z5,z36])]],
   [[(0,[z0,z1,z3,z4,z5,z522,z6]),(1,[z1,z3,z16,z4,z21,z6]),(0,[z0,z1,z3,z4,z523,z5,z6]),(0,[z0,z1,z3,z4,z524,z5,z6]),(0,[z0,z1,z3,z4,z5,z94,z6])],[(0,[z0,z1,z3,z4,z472,z51,z6]),(0,[z89,z0,z1,z336,z4,z5,z6]),(0,[z0,z525,z1,z3,z4,z5,z6]),(0,[z317,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z249,z6]),(0,[z95,z0,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z5,z6,z526]),(0,[z0,z1,z3,z147,z4,z21,z6]),(0,[z0,z1,z3,z4,z5,z6,z527]),(0,[z0,z1,z528,z3,z4,z5,z6])],[(0,[z15,z0,z1,z3,z4,z52,z6]),(0,[z0,z1,z529,z3,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z375,z36])],[(0,[z30,z0,z48,z3,z4,z5,z6]),(0,[z530,z0,z1,z3,z4,z5,z6]),(0,[z531,z0,z1,z3,z4,z5,z6]),(0,[z532,z0,z1,z3,z4,z5,z6]),(0,[z533,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z534,z6]),(0,[z535,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z536,z3,z4,z5,z6]),(0,[z0,z57,z1,z3,z4,z356,z6]),(0,[z0,z537,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z6,z538])],[(0,[z0,z1,z3,z539,z4,z5,z6]),(0,[z0,z1,z3,z540,z4,z5,z6]),(0,[z541,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z21,z55,z6]),(0,[z102,z0,z1,z3,z4,z51,z6]),(0,[z0,z1,z542,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z202,z4,z5,z6]),(0,[z0,z1,z3,z4,z318,z5,z221])],[(0,[z15,z18,z1,z3,z4,z5,z6]),(0,[z15,z1,z3,z4,z5,z49,z6]),(0,[z0,z1,z3,z4,z5,z438,z6]),(0,[z0,z1,z363,z3,z4,z21,z6]),(0,[z162,z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z199,z3,z4,z94,z6])]],
   [[(0,[z129,z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z131,z4,z21,z6]),(0,[z0,z1,z3,z4,z318,z21,z6]),(0,[z0,z1,z3,z20,z4,z5,z6]),(0,[z0,z1,z3,z4,z543,z5,z6]),(0,[z0,z1,z3,z544,z4,z5,z6]),(0,[z545,z0,z1,z3,z4,z5,z6])],[(1,[z0,z1,z3,z4,z178,z6]),(1,[z222,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z5,z546,z6]),(0,[z0,z40,z1,z3,z140,z5,z6]),(0,[z0,z1,z3,z4,z547,z5,z6])],[(0,[z548,z0,z1,z3,z4,z52,z6]),(0,[z0,z1,z549,z3,z4,z5,z6])],[(0,[z1,z3,z130,z4,z77,z5,z6]),(0,[z0,z1,z3,z4,z5,z21,z6]),(1,[z102,z0,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z5,z6,z42])],[(0,[z153,z0,z48,z3,z4,z5,z6]),(0,[z1,z3,z16,z4,z5,z21,z6]),(0,[z0,z1,z3,z4,z5,z550,z6]),(0,[z0,z1,z45,z3,z4,z5,z14])],[(0,[z551,z0,z1,z3,z4,z5,z6]),(0,[z162,z1,z3,z4,z77,z5,z6]),(0,[z552,z0,z1,z3,z4,z5,z6]),(0,[z0,z57,z1,z3,z394,z5,z6]),(0,[z0,z1,z3,z4,z553,z5,z6])],[(0,[z554,z0,z1,z3,z4,z5,z6]),(0,[z18,z0,z1,z3,z172,z5,z6]),(0,[z0,z1,z3,z4,z5,z555,z6]),(0,[z97,z0,z1,z3,z4,z51,z6]),(0,[z0,z57,z1,z3,z4,z5,z122]),(0,[z0,z1,z556,z3,z4,z5,z6])],[(0,[z0,z1,z48,z3,z4,z5,z6]),(0,[z0,z40,z1,z3,z4,z21,z6]),(0,[z89,z0,z1,z3,z4,z481,z6]),(0,[z0,z1,z3,z4,z205,z5,z6]),(0,[z0,z3,z4,z140,z5,z55,z6]),(0,[z1,z33,z72,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z557]),(0,[z0,z1,z3,z67,z4,z5,z6])]],
   [[(0,[z558,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z559,z4,z5,z6])],[(0,[z0,z560,z1,z3,z4,z5,z6]),(0,[z0,z1,z11,z3,z4,z51,z6]),(0,[z0,z1,z123,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z52,z83,z6]),(0,[z0,z1,z3,z561,z4,z5,z6])],[(0,[z95,z26,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z21,z94,z6]),(0,[z0,z1,z199,z3,z4,z21,z6]),(0,[z0,z1,z562,z3,z4,z5,z6]),(0,[z0,z1,z3,z563,z4,z5,z6]),(0,[z0,z564,z1,z3,z4,z5,z6]),(0,[z0,z1,z268,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z5,z565,z6])],[(0,[z0,z1,z48,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z5,z292,z6]),(0,[z0,z1,z566,z3,z4,z5,z6]),(0,[z0,z1,z3,z251,z4,z5,z6]),(0,[z30,z0,z1,z3,z4,z116,z6]),(0,[z0,z1,z3,z4,z567,z5,z6]),(0,[z0,z1,z3,z4,z52,z46,z6]),(0,[z0,z1,z3,z568,z4,z5,z6]),(0,[z135,z0,z1,z3,z4,z5,z6])],[(0,[z129,z0,z1,z3,z4,z51,z6]),(0,[z0,z1,z58,z3,z130,z5,z6]),(0,[z0,z1,z3,z131,z4,z51,z6]),(0,[z0,z1,z3,z4,z318,z51,z6])],[(0,[z0,z1,z3,z569,z4,z5,z6]),(0,[z0,z1,z3,z196,z4,z21,z6]),(0,[z0,z1,z3,z4,z5,z6,z468]),(0,[z0,z1,z3,z570,z4,z5,z6]),(0,[z0,z1,z33,z3,z202,z4,z6])],[(1,[z0,z1,z3,z172,z5,z6]),(0,[z571,z0,z1,z3,z4,z5,z6]),(0,[z65,z0,z1,z3,z20,z5,z6])],[(0,[z0,z48,z3,z4,z140,z5,z6]),(0,[z0,z572,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z5,z6,z310,z36])]],
   [[(0,[z0,z1,z573,z3,z4,z5,z6]),(0,[z574,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z130,z5,z6,z14]),(0,[z0,z225,z1,z3,z4,z263,z6]),(0,[z0,z1,z3,z140,z5,z46,z6]),(0,[z0,z1,z3,z4,z55,z6,z221]),(0,[z0,z1,z45,z3,z196,z5,z6]),(0,[z0,z1,z3,z4,z575,z5,z6]),(0,[z0,z1,z3,z4,z576,z5,z6]),(0,[z0,z1,z3,z4,z318,z12,z6])],[(0,[z0,z1,z3,z4,z577,z5,z6]),(0,[z95,z0,z1,z3,z4,z21,z6]),(0,[z63,z0,z1,z3,z4,z21,z6]),(0,[z208,z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z98,z3,z4,z55,z6]),(0,[z0,z57,z41,z3,z4,z5,z6]),(0,[z0,z1,z578,z3,z4,z5,z6]),(0,[z0,z1,z3,z579,z4,z5,z6])],[(0,[z222,z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z409,z4,z21,z6]),(0,[z22,z0,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z5,z6,z580]),(0,[z0,z1,z58,z3,z5,z46,z6]),(0,[z0,z581,z1,z3,z4,z5,z6]),(0,[z0,z1,z11,z3,z67,z4,z6]),(0,[z1,z3,z67,z462,z4,z5,z6])],[(0,[z26,z0,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z77,z140,z5,z6]),(0,[z0,z1,z3,z4,z21,z582,z6]),(0,[z0,z1,z3,z4,z5,z49,z6]),(0,[z583,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z123,z3,z103,z5,z6]),(0,[z0,z1,z3,z4,z5,z12,z6])],[(0,[z0,z584,z1,z3,z4,z5,z6]),(1,[z1,z3,z4,z21,z49,z6]),(0,[z0,z1,z45,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z52,z6,z14]),(1,[z0,z1,z3,z4,z422,z6]),(0,[z0,z1,z585,z3,z4,z5,z6])],[(0,[z586,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z21,z21,z6]),(0,[z0,z1,z3,z4,z21,z6,z42]),(0,[z30,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z54,z4,z52,z6]),(0,[z0,z1,z587,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z588,z5,z6]),(0,[z0,z1,z589,z3,z4,z5,z6]),(0,[z590,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z591,z4,z5,z6]),(0,[z89,z1,z3,z4,z5,z21,z6]),(0,[z22,z1,z3,z4,z5,z49,z6]),(1,[z0,z1,z3,z4,z5,z499]),(0,[z0,z1,z58,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z5,z6,z592])],[(0,[z593,z0,z1,z3,z4,z5,z6]),(0,[z63,z1,z3,z4,z77,z5,z6]),(0,[z129,z0,z1,z3,z4,z341,z6]),(0,[z0,z1,z3,z4,z5,z594,z6]),(1,[z0,z1,z3,z4,z263,z6])]],
   [[(0,[z162,z1,z3,z16,z4,z5,z6]),(0,[z0,z1,z3,z540,z4,z51,z6]),(0,[z0,z1,z3,z202,z4,z51,z6]),(1,[z0,z1,z336,z4,z5,z6]),(0,[z0,z225,z1,z147,z4,z5,z6]),(0,[z65,z0,z1,z3,z4,z52,z6]),(1,[z0,z57,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z595,z5,z6]),(0,[z0,z1,z3,z4,z596,z5,z6])],[(0,[z153,z0,z1,z3,z4,z464,z6]),(1,[z0,z1,z3,z4,z447,z6]),(0,[z89,z162,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z158,z596,z5,z6])],[(0,[z0,z1,z597,z3,z4,z5,z6]),(0,[z0,z1,z3,z20,z4,z51,z6]),(0,[z0,z1,z199,z3,z4,z12,z6])],[(0,[z0,z1,z3,z4,z598,z5,z6]),(0,[z0,z1,z3,z599,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z600])],[(0,[z0,z1,z3,z392,z4,z51,z6]),(0,[z0,z1,z3,z4,z5,z6,z601]),(0,[z0,z1,z3,z4,z5,z6,z602]),(0,[z603,z0,z1,z3,z4,z5,z6]),(1,[z1,z3,z4,z604,z5,z6])],[(0,[z153,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z35,z3,z4,z5,z6])],[(0,[z95,z0,z57,z3,z4,z5,z6]),(0,[z17,z0,z1,z3,z4,z5,z6]),(0,[z222,z0,z1,z3,z4,z51,z6]),(1,[z0,z40,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z5,z605,z6])],[(0,[z606,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z52,z6,z36]),(0,[z0,z57,z3,z4,z5,z122,z6]),(0,[z607,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z608,z4,z5,z6])]],
   [[(0,[z95,z0,z1,z3,z4,z419,z6]),(0,[z0,z1,z123,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z5,z356,z6])],[(0,[z0,z1,z211,z3,z4,z5,z6]),(0,[z609,z0,z1,z3,z4,z5,z6]),(0,[z610,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z52,z52,z6]),(0,[z0,z1,z611,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z612,z5,z6]),(0,[z0,z1,z3,z202,z67,z4,z6])],[(0,[z0,z1,z3,z613,z4,z5,z6]),(0,[z0,z1,z74,z4,z5,z6,z36]),(0,[z0,z1,z3,z4,z77,z55,z6]),(0,[z89,z0,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z55,z6,z101]),(0,[z0,z1,z3,z614,z4,z5,z6]),(0,[z65,z0,z3,z4,z140,z5,z6]),(0,[z0,z1,z3,z4,z5,z83,z42]),(0,[z0,z1,z615,z3,z4,z5,z6])],[(0,[z616,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z366,z6])],[(0,[z0,z1,z3,z4,z328,z21,z6]),(0,[z0,z1,z3,z4,z51,z96,z6]),(0,[z0,z1,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z617,z4,z5,z6]),(0,[z0,z1,z3,z618,z4,z5,z6]),(1,[z84,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z619,z6]),(0,[z0,z1,z427,z3,z4,z51,z6]),(0,[z0,z1,z45,z3,z140,z5,z6]),(0,[z0,z1,z3,z4,z5,z293,z6]),(0,[z112,z0,z1,z3,z4,z52,z6]),(0,[z620,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z501,z4,z5,z6]),(0,[z0,z1,z3,z188,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z13])],[(0,[z0,z1,z3,z147,z4,z55,z6]),(0,[z621,z0,z1,z3,z4,z5,z6]),(0,[z97,z0,z1,z3,z4,z55,z6])],[(0,[z0,z1,z3,z4,z622,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z623]),(1,[z518,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z103,z5,z6]),(0,[z0,z1,z3,z4,z5,z34,z6]),(0,[z0,z1,z3,z4,z624,z5,z6])]],
   [[(0,[z153,z129,z1,z3,z4,z5,z6]),(0,[z625,z0,z1,z3,z4,z5,z6]),(1,[z1,z3,z4,z77,z21,z6]),(0,[z0,z1,z98,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z500,z55,z6]),(0,[z0,z1,z626,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z51,z348,z6]),(0,[z0,z81,z1,z3,z4,z5,z6]),(0,[z0,z1,z627,z3,z4,z5,z6]),(0,[z0,z40,z1,z3,z4,z183,z6]),(0,[z0,z1,z3,z4,z5,z628,z6]),(0,[z0,z1,z494,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z122,z36]),(0,[z0,z1,z3,z4,z5,z6,z629])],[(0,[z630,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z21,z83,z6]),(0,[z0,z1,z3,z4,z51,z6,z14]),(0,[z0,z631,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z21,z85,z6]),(1,[z0,z1,z3,z4,z328,z6]),(0,[z0,z1,z45,z3,z4,z21,z6]),(0,[z162,z0,z1,z3,z4,z55,z6]),(0,[z632,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z11,z3,z4,z158,z6]),(0,[z0,z633,z1,z3,z4,z5,z6])],[(0,[z129,z0,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z21,z46,z6]),(0,[z0,z1,z3,z131,z4,z55,z6]),(0,[z0,z1,z3,z4,z318,z55,z6])],[(0,[z18,z1,z3,z4,z5,z21,z6]),(0,[z0,z1,z3,z4,z51,z6,z143]),(0,[z0,z1,z3,z4,z604,z5,z6])],[(0,[z0,z1,z3,z634,z4,z5,z6]),(0,[z0,z635,z1,z3,z4,z5,z6]),(1,[z0,z98,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z140,z5,z6]),(0,[z636,z0,z1,z3,z4,z5,z6]),(0,[z91,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z637,z4,z5,z6]),(0,[z0,z1,z3,z638,z4,z5,z6]),(0,[z0,z1,z3,z202,z4,z5,z12])],[(0,[z639,z0,z1,z3,z4,z5,z6]),(0,[z360,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z55,z6]),(0,[z0,z1,z640,z3,z4,z5,z6])]],
   [[(0,[z18,z162,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z196,z130,z5,z6]),(0,[z89,z0,z1,z3,z4,z415,z6]),(0,[z0,z1,z641,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z642]),(0,[z0,z1,z3,z4,z5,z6,z643])],[(0,[z18,z1,z48,z3,z4,z5,z6]),(0,[z644,z0,z1,z3,z4,z5,z6]),(0,[z0,z41,z1,z3,z4,z52,z6]),(1,[z0,z1,z3,z4,z53,z6]),(0,[z0,z1,z3,z4,z5,z645,z6]),(0,[z243,z0,z1,z4,z5,z6,z36])],[(0,[z646,z0,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z164,z6]),(0,[z636,z0,z1,z3,z4,z52,z6]),(1,[z0,z1,z218,z3,z4,z6]),(0,[z0,z1,z3,z647,z4,z5,z6])],[(0,[z0,z1,z3,z4,z51,z5,z6]),(1,[z89,z1,z3,z4,z21,z6]),(0,[z30,z81,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z116,z6]),(0,[z0,z648,z1,z3,z4,z5,z6])],[(0,[z95,z0,z98,z3,z4,z5,z6]),(0,[z63,z0,z1,z3,z130,z5,z6]),(0,[z0,z1,z3,z480,z4,z21,z6]),(0,[z0,z1,z3,z4,z5,z274,z6]),(0,[z0,z1,z3,z4,z5,z499,z6]),(0,[z0,z1,z649,z3,z4,z5,z6]),(0,[z169,z0,z3,z4,z103,z5,z6])],[(0,[z18,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z650,z3,z4,z5,z6]),(0,[z102,z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z51,z6,z36]),(0,[z0,z1,z33,z3,z4,z5,z6]),(1,[z0,z3,z4,z596,z5,z6]),(0,[z236,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z196,z4,z5,z46])],[(0,[z0,z1,z3,z16,z4,z52,z6]),(0,[z0,z1,z3,z4,z5,z6,z651]),(0,[z0,z225,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z55,z122,z6])],[(0,[z0,z1,z35,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z51,z52,z6]),(0,[z0,z1,z3,z4,z5,z652,z6])]],
   [[(0,[z0,z1,z3,z653,z4,z5,z6]),(0,[z0,z1,z3,z654,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z655,z6]),(0,[z0,z1,z3,z4,z5,z6,z656]),(0,[z0,z1,z657,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z658,z6])],[(0,[z26,z0,z48,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z464,z6]),(0,[z0,z1,z3,z4,z5,z659,z6]),(0,[z0,z40,z41,z3,z4,z5,z6]),(0,[z0,z1,z3,z196,z4,z55,z6]),(0,[z0,z1,z3,z4,z52,z6,z221]),(0,[z0,z1,z3,z4,z5,z6,z660]),(0,[z0,z1,z3,z661,z4,z5,z6]),(0,[z0,z1,z3,z662,z4,z5,z6])],[(0,[z15,z0,z1,z3,z4,z5,z6]),(0,[z0,z225,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z20,z4,z55,z6]),(0,[z0,z1,z3,z4,z5,z122,z83])],[(0,[z0,z98,z3,z147,z4,z5,z6]),(0,[z0,z41,z3,z4,z140,z5,z6]),(0,[z0,z1,z3,z4,z5,z423,z6]),(0,[z0,z458,z1,z3,z4,z5,z6])],[(0,[z153,z26,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z6])],[(1,[z0,z1,z3,z4,z5,z6]),(0,[z63,z0,z1,z3,z4,z55,z6]),(0,[z97,z0,z1,z3,z4,z21,z6]),(1,[z30,z0,z3,z4,z55,z6]),(0,[z0,z1,z3,z131,z140,z5,z6]),(0,[z0,z1,z400,z3,z4,z55,z6]),(0,[z0,z3,z4,z5,z55,z6,z42]),(0,[z0,z1,z3,z4,z52,z272,z6]),(0,[z663,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z664,z6]),(1,[z0,z1,z3,z4,z372,z6]),(0,[z0,z1,z3,z665,z4,z5,z6])],[(0,[z0,z1,z666,z3,z4,z5,z6]),(1,[z0,z211,z3,z4,z5,z6]),(0,[z0,z1,z3,z667,z4,z5,z6]),(0,[z222,z0,z1,z3,z4,z55,z6]),(0,[z668,z0,z1,z3,z4,z5,z6]),(0,[z0,z669,z1,z3,z4,z5,z6])],[(0,[z0,z1,z670,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z434,z6]),(0,[z0,z1,z3,z671,z4,z5,z6])]],
   [[(0,[z390,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z11,z3,z4,z21,z6]),(0,[z672,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z78,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z673,z6]),(0,[z0,z674,z1,z3,z4,z5,z6]),(0,[z0,z82,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z310]),(1,[z0,z1,z3,z298,z4,z6]),(0,[z675,z0,z1,z3,z4,z5,z6]),(0,[z676,z0,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z318,z604,z5,z6])],[(0,[z677,z0,z1,z3,z4,z5,z6]),(0,[z548,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z335,z4,z5,z6]),(0,[z0,z1,z3,z4,z103,z51,z6]),(0,[z0,z1,z484,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z622,z51,z6]),(0,[z65,z518,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z678])],[(0,[z0,z1,z3,z4,z5,z6,z679]),(0,[z0,z1,z3,z680,z4,z5,z6]),(1,[z0,z3,z501,z4,z5,z6]),(0,[z0,z1,z681,z3,z4,z5,z6])],[(1,[z26,z48,z3,z4,z5,z6]),(0,[z0,z1,z682,z3,z4,z5,z6]),(0,[z0,z1,z3,z683,z4,z5,z6]),(0,[z0,z1,z123,z3,z130,z5,z6]),(0,[z0,z1,z414,z3,z4,z5,z6]),(0,[z684,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z55,z546,z6]),(1,[z383,z1,z3,z4,z5,z6])],[(0,[z685,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z686,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z582,z6]),(0,[z0,z225,z1,z3,z4,z365,z6]),(0,[z0,z1,z3,z20,z103,z5,z6])],[(0,[z0,z687,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z516,z4,z21,z6]),(0,[z0,z1,z3,z4,z230,z52,z6]),(0,[z0,z1,z3,z4,z52,z6,z295]),(0,[z0,z1,z688,z3,z4,z5,z6]),(0,[z689,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z690,z6]),(0,[z0,z1,z691,z3,z4,z5,z6])],[(1,[z0,z146,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z481,z5,z6]),(0,[z0,z1,z3,z4,z55,z550,z6])],[(0,[z0,z1,z3,z692,z4,z5,z6]),(0,[z0,z1,z3,z693,z4,z5,z6]),(0,[z0,z1,z3,z694,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z255,z6]),(0,[z0,z3,z4,z5,z6,z177,z36])]],
   [[(0,[z0,z1,z3,z4,z140,z51,z6]),(0,[z243,z0,z1,z3,z4,z52,z6]),(0,[z367,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z188,z67,z4,z6])],[(0,[z0,z1,z3,z4,z5,z695,z6]),(0,[z0,z1,z696,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z308,z5,z6]),(0,[z30,z173,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z214,z6]),(0,[z0,z1,z3,z4,z158,z52,z6]),(0,[z0,z1,z123,z3,z5,z46,z6]),(0,[z0,z1,z3,z4,z5,z6,z697])],[(0,[z153,z0,z1,z3,z4,z144,z6]),(0,[z0,z1,z3,z130,z4,z5,z6]),(0,[z0,z1,z3,z4,z249,z52,z6]),(0,[z97,z0,z57,z3,z4,z5,z6])],[(0,[z698,z0,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z77,z5,z6,z14]),(0,[z0,z1,z3,z4,z21,z659,z6]),(0,[z0,z1,z3,z4,z52,z6,z101]),(1,[z0,z1,z3,z4,z365,z6]),(0,[z0,z1,z3,z699,z4,z5,z6])],[(0,[z0,z700,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z381,z6]),(0,[z0,z1,z3,z4,z5,z6,z701]),(0,[z0,z1,z3,z4,z423,z6,z14])],[(0,[z0,z1,z3,z4,z319,z5,z6]),(0,[z63,z0,z1,z3,z4,z434,z6]),(0,[z0,z3,z202,z346,z4,z5,z6]),(0,[z0,z1,z3,z202,z4,z5,z221]),(0,[z0,z1,z3,z4,z5,z6,z702])],[(0,[z0,z0,z1,z3,z4,z5,z6]),(0,[z26,z1,z48,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z5,z6,z703]),(0,[z0,z1,z3,z4,z5,z704,z6]),(0,[z0,z1,z3,z130,z4,z52,z6]),(0,[z89,z0,z1,z3,z157,z5,z6]),(0,[z0,z1,z3,z705,z4,z5,z6])],[(1,[z0,z1,z3,z4,z257,z6]),(0,[z0,z1,z3,z202,z4,z21,z6]),(0,[z0,z1,z33,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z51,z6,z221]),(0,[z0,z428,z1,z3,z4,z5,z6]),(1,[z0,z1,z3,z4,z415,z6]),(0,[z0,z1,z3,z706,z4,z5,z6]),(0,[z0,z57,z1,z3,z4,z52,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z1,z3,z4,z249,z53,z6]),(0,[z1,z3,z462,z4,z21,z6]),(0,[z0,z518,z3,z140,z5,z6]),(0,[z0,z1,z3,z4,z707,z6]),(0,[z1,z3,z4,z55,z6,z375]),(0,[z0,z141,z3,z4,z52,z6]),(0,[z0,z3,z708,z4,z5,z6])],[(0,[z0,z1,z3,z157,z5,z6]),(0,[z0,z3,z4,z328,z55,z6]),(0,[z518,z1,z3,z4,z709,z6]),(0,[z0,z267,z3,z4,z596,z6])],[(0,[z0,z1,z3,z4,z328,z6]),(0,[z0,z1,z3,z335,z19,z6]),(0,[z0,z1,z710,z4,z55,z6]),(0,[z0,z458,z3,z4,z55,z6]),(0,[z711,z1,z3,z4,z52,z6])],[(0,[z266,z1,z16,z4,z5,z6]),(0,[z135,z1,z3,z77,z5,z6]),(0,[z0,z3,z140,z55,z46,z6]),(0,[z0,z1,z3,z4,z712,z6]),(0,[z0,z1,z713,z3,z5,z6]),(0,[z0,z3,z4,z311,z714,z6])],[(0,[z89,z1,z3,z4,z5,z238]),(0,[z0,z1,z3,z715,z5,z6]),(0,[z0,z1,z3,z31,z116,z6]),(0,[z0,z1,z3,z4,z716,z6]),(0,[z0,z631,z3,z4,z55,z6]),(0,[z717,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z718,z6])],[(0,[z173,z1,z3,z4,z5,z6]),(0,[z0,z90,z3,z172,z5,z6]),(0,[z1,z3,z4,z5,z719,z101]),(0,[z0,z3,z191,z5,z55,z6]),(0,[z0,z458,z3,z4,z200,z6]),(0,[z367,z236,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z720,z6]),(0,[z18,z1,z3,z4,z144,z6]),(0,[z0,z1,z3,z4,z721,z6]),(0,[z0,z1,z3,z251,z481,z6]),(0,[z0,z1,z3,z722,z4,z6]),(0,[z0,z1,z3,z4,z5,z723]),(0,[z198,z1,z3,z4,z724,z6]),(0,[z0,z1,z3,z4,z725,z6]),(0,[z0,z1,z3,z726,z55,z6]),(0,[z0,z1,z3,z4,z727,z6]),(0,[z0,z1,z33,z4,z378,z6])],[(0,[z0,z64,z3,z4,z728,z6]),(0,[z22,z1,z3,z4,z21,z49]),(0,[z29,z0,z3,z4,z85,z6]),(0,[z0,z1,z3,z4,z51,z499]),(0,[z1,z3,z729,z4,z5,z6]),(0,[z1,z3,z392,z4,z604,z6])]],
   [[(0,[z30,z0,z654,z4,z5,z6]),(0,[z0,z1,z3,z4,z55,z439]),(0,[z30,z0,z3,z4,z366,z6]),(0,[z730,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z394,z55,z6])],[(0,[z213,z48,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z731,z6]),(0,[z0,z1,z336,z4,z51,z6]),(0,[z518,z1,z3,z4,z259,z6]),(0,[z0,z3,z4,z191,z55,z6]),(0,[z169,z0,z3,z4,z732,z6]),(0,[z0,z1,z218,z3,z4,z6])],[(0,[z95,z0,z3,z205,z5,z6]),(1,[z211,z3,z77,z5,z6]),(0,[z89,z1,z3,z4,z21,z6]),(0,[z0,z146,z3,z157,z5,z6]),(0,[z30,z0,z3,z4,z293,z6]),(0,[z0,z41,z3,z4,z183,z6]),(0,[z0,z1,z3,z733,z55,z6]),(0,[z128,z0,z3,z4,z55,z6]),(0,[z97,z0,z3,z4,z52,z42]),(0,[z82,z1,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z734,z6])],[(0,[z0,z735,z3,z4,z5,z6]),(0,[z211,z3,z4,z5,z49,z6]),(0,[z1,z736,z3,z4,z55,z6]),(0,[z0,z525,z3,z4,z52,z6])],[(0,[z93,z48,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z737,z6]),(0,[z0,z1,z3,z4,z738,z6]),(0,[z0,z1,z739,z4,z5,z6]),(0,[z0,z1,z3,z4,z740,z6]),(0,[z0,z3,z4,z471,z55,z6]),(0,[z0,z611,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z741,z6])],[(0,[z153,z1,z3,z157,z5,z6]),(0,[z129,z1,z3,z4,z328,z6]),(0,[z1,z3,z4,z604,z51,z6]),(0,[z0,z1,z3,z4,z742,z6]),(0,[z743,z1,z3,z4,z52,z6]),(0,[z1,z3,z744,z4,z5,z6])],[(0,[z0,z1,z3,z31,z5,z6]),(0,[z30,z0,z3,z31,z55,z6]),(0,[z745,z1,z3,z4,z5,z6])],[(0,[z1,z3,z4,z523,z21,z6]),(0,[z0,z1,z3,z4,z746,z6]),(0,[z0,z211,z3,z4,z747,z6]),(0,[z30,z0,z147,z4,z5,z499]),(0,[z0,z3,z4,z55,z6,z601]),(0,[z0,z3,z476,z4,z55,z6]),(0,[z0,z748,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z749,z6]),(0,[z0,z1,z3,z4,z192,z6]),(0,[z0,z750,z3,z4,z5,z6]),(0,[z1,z3,z4,z21,z658,z6]),(0,[z0,z1,z3,z191,z52,z6]),(0,[z1,z3,z462,z4,z12,z6]),(0,[z0,z1,z3,z5,z6,z751])],[(0,[z1,z752,z16,z4,z5,z6]),(0,[z0,z1,z3,z205,z5,z499]),(0,[z0,z1,z3,z4,z753,z6])],[(0,[z0,z1,z3,z76,z100,z6]),(0,[z15,z1,z336,z4,z5,z6]),(0,[z0,z1,z125,z3,z21,z6]),(0,[z0,z3,z754,z4,z5,z6]),(0,[z0,z1,z3,z4,z755,z6]),(0,[z30,z0,z235,z4,z5,z6]),(0,[z0,z1,z3,z4,z756,z6]),(0,[z198,z1,z3,z4,z52,z6]),(0,[z757,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z758,z6]),(0,[z89,z146,z3,z4,z21,z6]),(0,[z0,z1,z187,z4,z34,z6]),(0,[z0,z1,z3,z157,z415,z6]),(0,[z0,z1,z3,z4,z759,z6]),(0,[z760,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z761,z4,z6]),(0,[z0,z1,z3,z762,z4,z6])],[(0,[z0,z1,z3,z4,z5,z6]),(0,[z616,z48,z3,z4,z5,z6]),(0,[z153,z1,z3,z4,z53,z6]),(0,[z129,z1,z3,z4,z763,z6]),(0,[z367,z1,z3,z4,z21,z6]),(0,[z317,z1,z3,z4,z21,z6]),(0,[z30,z0,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z764,z6]),(0,[z765,z1,z3,z4,z5,z6]),(0,[z243,z0,z1,z4,z5,z766])],[(0,[z1,z3,z4,z77,z85,z6]),(0,[z1,z3,z539,z4,z21,z6]),(0,[z1,z3,z540,z4,z21,z6]),(0,[z1,z385,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z767,z6]),(0,[z0,z768,z3,z4,z5,z6]),(0,[z0,z3,z4,z140,z359,z6]),(0,[z84,z1,z3,z4,z51,z6]),(0,[z0,z3,z4,z55,z83,z42]),(0,[z97,z0,z3,z4,z381,z42]),(0,[z769,z0,z3,z4,z5,z6]),(0,[z367,z3,z4,z5,z6,z177])],[(0,[z770,z1,z3,z4,z5,z6]),(0,[z65,z0,z3,z140,z366,z6]),(0,[z0,z1,z3,z771,z5,z6]),(0,[z1,z3,z4,z772,z5,z6]),(0,[z0,z773,z3,z4,z5,z6]),(0,[z0,z125,z3,z5,z6,z177]),(0,[z0,z774,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z775,z6])],[(0,[z28,z0,z1,z4,z5,z36]),(0,[z0,z1,z3,z776,z5,z6]),(0,[z0,z1,z3,z4,z709,z6]),(0,[z1,z3,z4,z777,z5,z6]),(0,[z0,z1,z3,z298,z4,z6]),(0,[z0,z778,z3,z4,z5,z6])]],
   [[(0,[z18,z1,z3,z4,z192,z6]),(0,[z0,z779,z3,z4,z5,z6]),(0,[z1,z3,z172,z5,z21,z6]),(0,[z780,z0,z3,z4,z21,z6]),(0,[z518,z1,z3,z4,z51,z6]),(0,[z135,z1,z3,z4,z51,z6]),(0,[z0,z3,z20,z205,z5,z6]),(0,[z0,z1,z3,z4,z781,z6]),(0,[z0,z1,z3,z54,z4,z295]),(0,[z0,z3,z4,z111,z52,z6]),(0,[z91,z1,z3,z4,z782,z6])],[(0,[z1,z74,z336,z4,z5,z6]),(0,[z0,z584,z3,z140,z5,z6]),(0,[z1,z3,z392,z4,z21,z6]),(0,[z689,z1,z3,z4,z21,z6]),(0,[z0,z458,z3,z4,z21,z6]),(0,[z0,z1,z3,z202,z4,z143]),(0,[z0,z3,z4,z140,z55,z6]),(0,[z0,z3,z332,z4,z5,z42]),(0,[z0,z3,z346,z4,z52,z6]),(0,[z0,z1,z3,z67,z512,z6]),(0,[z1,z3,z5,z6,z310,z375]),(0,[z3,z462,z501,z4,z5,z6])],[(0,[z95,z0,z3,z4,z5,z439]),(0,[z383,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z596,z21,z6]),(0,[z89,z1,z3,z4,z5,z101]),(0,[z0,z783,z3,z4,z5,z6]),(0,[z0,z1,z784,z103,z5,z6]),(0,[z0,z1,z3,z4,z785,z6]),(0,[z1,z3,z188,z462,z4,z6])],[(0,[z0,z1,z3,z4,z786,z6]),(0,[z0,z193,z3,z4,z55,z6]),(0,[z0,z1,z787,z4,z5,z6]),(0,[z0,z1,z3,z157,z51,z6]),(0,[z0,z1,z3,z4,z788,z6]),(0,[z0,z1,z789,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z790]),(0,[z0,z3,z4,z5,z122,z439]),(0,[z0,z1,z3,z4,z791,z6]),(0,[z0,z3,z501,z4,z94,z6])],[(0,[z0,z146,z3,z4,z5,z6]),(0,[z1,z3,z665,z4,z51,z6]),(0,[z0,z1,z414,z4,z481,z6]),(0,[z792,z0,z3,z4,z5,z6]),(0,[z30,z0,z98,z4,z55,z6]),(0,[z0,z1,z3,z4,z793,z6]),(0,[z0,z1,z58,z422,z103,z6]),(0,[z0,z1,z3,z4,z794,z6]),(0,[z0,z3,z4,z714,z6,z14])],[(0,[z0,z1,z3,z4,z795,z6]),(0,[z0,z796,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z797,z6]),(0,[z0,z1,z3,z4,z798,z6]),(0,[z0,z1,z3,z4,z799,z6]),(0,[z0,z1,z3,z4,z800,z6]),(0,[z0,z1,z3,z4,z801,z6]),(0,[z0,z1,z3,z4,z802,z6]),(0,[z1,z72,z3,z4,z622,z6]),(1,[z0,z3,z4,z714,z6])],[(0,[z0,z1,z3,z803,z5,z6]),(0,[z0,z48,z3,z205,z5,z6]),(0,[z0,z1,z3,z172,z55,z6]),(0,[z0,z1,z804,z4,z5,z6]),(0,[z243,z0,z1,z4,z21,z36]),(0,[z0,z3,z4,z359,z6,z42]),(0,[z0,z1,z3,z4,z805,z6]),(0,[z169,z0,z3,z20,z5,z6]),(0,[z0,z1,z3,z332,z4,z221]),(0,[z0,z1,z3,z52,z6,z310]),(0,[z0,z1,z3,z4,z806,z6]),(0,[z807,z1,z3,z4,z5,z6]),(0,[z135,z808,z3,z4,z5,z6])]],
   [[(0,[z0,z1,z3,z4,z809,z6]),(0,[z105,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z810,z6]),(0,[z811,z0,z3,z4,z5,z6]),(0,[z367,z1,z3,z5,z6,z310])],[(0,[z0,z1,z3,z812,z5,z6]),(0,[z63,z1,z3,z157,z5,z6]),(0,[z1,z3,z563,z4,z21,z6]),(0,[z0,z1,z813,z3,z4,z6]),(0,[z0,z428,z414,z4,z5,z6]),(0,[z0,z428,z3,z4,z481,z6]),(0,[z0,z1,z3,z251,z52,z6]),(0,[z0,z1,z3,z4,z814,z6]),(0,[z0,z1,z3,z815,z5,z6]),(0,[z816,z1,z3,z4,z5,z6]),(0,[z817,z1,z3,z4,z5,z6]),(0,[z0,z3,z818,z4,z5,z6]),(0,[z0,z1,z3,z819,z5,z6])],[(0,[z0,z1,z3,z820,z5,z6]),(0,[z0,z1,z3,z4,z821,z6]),(0,[z65,z0,z3,z140,z55,z6]),(0,[z1,z72,z3,z4,z52,z6]),(0,[z0,z411,z3,z4,z52,z6]),(0,[z1,z3,z4,z311,z6,z13])],[(0,[z0,z1,z3,z5,z6,z822]),(0,[z0,z1,z3,z823,z5,z6]),(0,[z0,z211,z3,z4,z21,z6]),(0,[z0,z211,z3,z4,z824,z6]),(0,[z1,z3,z77,z21,z6,z14]),(0,[z89,z146,z3,z4,z5,z101]),(0,[z0,z3,z4,z5,z6,z177]),(0,[z0,z1,z825,z3,z4,z6]),(0,[z0,z3,z4,z55,z6,z642]),(0,[z0,z33,z3,z346,z4,z6]),(0,[z236,z0,z125,z3,z5,z6])],[(0,[z15,z1,z16,z4,z192,z6]),(0,[z242,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z826,z6]),(0,[z0,z827,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z828,z6]),(0,[z0,z1,z187,z4,z659,z6]),(0,[z0,z218,z3,z4,z23,z6])],[(0,[z0,z1,z3,z4,z257,z6]),(0,[z1,z3,z4,z5,z829,z6]),(0,[z0,z1,z3,z4,z830,z6]),(0,[z173,z1,z3,z4,z831,z6]),(0,[z1,z832,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z833,z6]),(0,[z411,z3,z462,z4,z5,z6])],[(0,[z213,z1,z3,z77,z5,z6]),(0,[z0,z3,z501,z4,z21,z6]),(0,[z0,z1,z3,z4,z55,z499]),(0,[z0,z1,z3,z298,z6,z310])]],
   [[(0,[z0,z1,z3,z4,z834,z6]),(0,[z835,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z23,z5,z6]),(0,[z0,z3,z131,z140,z55,z6]),(0,[z0,z3,z4,z422,z23,z6])],[(0,[z0,z1,z336,z4,z55,z6]),(0,[z0,z529,z3,z4,z55,z6]),(0,[z0,z1,z45,z3,z5,z580]),(0,[z169,z0,z3,z4,z52,z6]),(0,[z1,z3,z4,z52,z6,z375]),(0,[z84,z1,z3,z67,z94,z6])],[(0,[z0,z1,z3,z4,z292,z6]),(0,[z0,z1,z3,z836,z5,z6]),(0,[z18,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z837,z6]),(0,[z0,z3,z4,z838,z5,z6]),(0,[z1,z3,z77,z140,z21,z6]),(0,[z1,z832,z3,z4,z52,z6]),(0,[z0,z839,z3,z4,z5,z6]),(0,[z1,z33,z3,z462,z4,z6])],[(0,[z0,z840,z3,z4,z5,z6]),(0,[z1,z585,z3,z4,z21,z6]),(0,[z841,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z842,z6]),(0,[z843,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z844,z4,z6]),(0,[z0,z1,z3,z4,z845,z6])],[(0,[z0,z1,z3,z4,z846,z6]),(0,[z1,z587,z3,z4,z21,z6]),(0,[z89,z1,z3,z4,z415,z101]),(0,[z81,z1,z3,z31,z5,z6]),(0,[z30,z0,z147,z4,z116,z6]),(0,[z0,z1,z4,z784,z5,z6])],[(0,[z0,z1,z3,z149,z5,z6]),(0,[z1,z3,z591,z4,z21,z6]),(0,[z0,z1,z3,z847,z5,z6]),(0,[z564,z1,z3,z4,z51,z6]),(0,[z1,z3,z4,z55,z6,z13]),(0,[z1,z3,z4,z604,z55,z6]),(0,[z0,z132,z3,z4,z52,z6])],[(0,[z0,z1,z3,z4,z51,z6]),(0,[z0,z3,z4,z328,z85,z6]),(0,[z367,z1,z16,z4,z5,z6]),(0,[z135,z1,z3,z157,z5,z6]),(0,[z0,z1,z3,z205,z116,z6]),(0,[z0,z1,z3,z4,z56,z439]),(0,[z848,z1,z3,z4,z55,z6])],[(0,[z1,z3,z16,z4,z53,z6]),(0,[z0,z211,z3,z4,z51,z6]),(0,[z0,z768,z3,z4,z51,z6]),(0,[z0,z1,z3,z251,z415,z6]),(0,[z0,z1,z33,z4,z34,z6]),(0,[z1,z849,z3,z4,z5,z6]),(0,[z0,z3,z346,z4,z318,z6])]],
   [[(0,[z17,z0,z3,z4,z52,z6]),(0,[z1,z3,z4,z274,z49,z6]),(0,[z0,z691,z3,z4,z55,z6])],[(0,[z0,z48,z3,z4,z359,z6]),(0,[z0,z3,z850,z4,z5,z6]),(0,[z0,z1,z851,z3,z4,z6]),(0,[z0,z3,z346,z4,z6,z221])],[(0,[z0,z1,z3,z4,z319,z6]),(0,[z81,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z852,z6]),(0,[z0,z853,z3,z4,z5,z6]),(0,[z129,z1,z3,z77,z21,z6]),(0,[z0,z161,z3,z4,z52,z6]),(0,[z1,z3,z4,z598,z21,z6]),(0,[z0,z1,z3,z4,z854,z6])],[(0,[z26,z48,z3,z149,z5,z6]),(0,[z278,z1,z3,z77,z5,z6]),(0,[z610,z1,z3,z4,z21,z6]),(0,[z0,z3,z4,z5,z6,z855]),(0,[z30,z0,z343,z4,z5,z6]),(1,[z518,z3,z140,z5,z6]),(0,[z856,z1,z3,z4,z5,z6]),(0,[z236,z0,z3,z4,z372,z6])],[(0,[z91,z1,z3,z4,z5,z6]),(0,[z26,z48,z3,z4,z51,z6]),(0,[z0,z90,z3,z4,z5,z6]),(0,[z0,z1,z3,z857,z5,z6]),(0,[z0,z858,z3,z4,z5,z6]),(0,[z0,z859,z3,z4,z5,z6]),(0,[z603,z1,z3,z4,z21,z6]),(0,[z89,z1,z3,z4,z51,z101]),(0,[z383,z1,z3,z4,z51,z6]),(0,[z0,z1,z4,z5,z6,z860]),(0,[z0,z1,z3,z4,z861,z6]),(0,[z0,z1,z3,z4,z862,z6])],[(0,[z0,z3,z4,z21,z6,z177]),(0,[z0,z3,z863,z4,z5,z6]),(0,[z0,z1,z3,z4,z864,z6]),(0,[z0,z1,z3,z4,z865,z6]),(0,[z0,z3,z4,z205,z55,z6]),(0,[z0,z141,z3,z4,z116,z6]),(0,[z383,z1,z33,z4,z34,z6]),(0,[z0,z1,z3,z866,z4,z6]),(0,[z0,z808,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z867,z6]),(0,[z15,z1,z16,z4,z21,z6]),(0,[z0,z1,z3,z172,z21,z6]),(0,[z0,z1,z3,z4,z868,z6]),(0,[z30,z0,z147,z4,z5,z6]),(0,[z0,z1,z3,z4,z869,z6]),(0,[z0,z1,z3,z844,z94,z6])],[(0,[z0,z146,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z870,z6]),(0,[z0,z1,z3,z4,z871,z6]),(0,[z236,z0,z3,z4,z52,z6]),(0,[z0,z3,z501,z4,z12,z6])]],
   [[(0,[z0,z1,z3,z4,z100,z6]),(0,[z26,z48,z3,z4,z319,z6]),(0,[z222,z1,z3,z4,z53,z6]),(0,[z1,z3,z4,z21,z96,z6]),(0,[z30,z0,z3,z205,z55,z6]),(0,[z209,z0,z3,z4,z55,z6]),(0,[z518,z1,z3,z4,z55,z6])],[(0,[z0,z1,z3,z4,z872,z6]),(0,[z0,z3,z4,z55,z6,z42]),(0,[z0,z3,z568,z4,z55,z6]),(0,[z1,z72,z3,z202,z4,z6]),(0,[z1,z3,z4,z800,z6,z13])],[(0,[z0,z1,z3,z4,z873,z6]),(0,[z260,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z5,z874]),(0,[z0,z400,z98,z4,z55,z6]),(0,[z875,z0,z3,z4,z5,z6]),(0,[z0,z3,z121,z501,z4,z6]),(0,[z0,z1,z45,z3,z5,z14])],[(0,[z0,z1,z3,z876,z5,z6]),(0,[z0,z1,z3,z877,z5,z6]),(0,[z89,z1,z3,z4,z274,z6]),(0,[z0,z1,z3,z878,z5,z6]),(0,[z0,z3,z202,z346,z4,z221]),(0,[z0,z1,z3,z202,z4,z221])],[(0,[z0,z1,z3,z4,z5,z879]),(0,[z0,z1,z3,z4,z880,z5]),(0,[z0,z428,z3,z4,z52,z6]),(0,[z0,z1,z3,z205,z52,z6]),(0,[z0,z1,z3,z4,z881,z6]),(0,[z65,z198,z3,z140,z5,z6])],[(0,[z153,z1,z3,z76,z5,z6]),(0,[z0,z1,z3,z4,z882,z6]),(0,[z0,z1,z883,z3,z4,z5]),(0,[z0,z1,z3,z884,z5,z6]),(0,[z0,z885,z147,z4,z5,z6]),(0,[z0,z1,z3,z4,z886,z6]),(0,[z0,z1,z3,z4,z887,z6]),(0,[z0,z1,z33,z4,z329,z6]),(0,[z236,z0,z3,z4,z5,z42]),(0,[z169,z888,z3,z4,z5,z6]),(0,[z0,z889,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z890,z6]),(0,[z1,z3,z4,z622,z21,z6]),(0,[z0,z1,z3,z4,z891,z6]),(0,[z0,z1,z3,z892,z5,z6]),(0,[z0,z3,z4,z893,z5,z6]),(0,[z0,z1,z3,z4,z21,z499]),(0,[z0,z1,z3,z4,z894,z6]),(0,[z0,z1,z3,z895,z5,z6]),(0,[z0,z57,z3,z4,z381,z6])],[(0,[z0,z1,z3,z76,z21,z6]),(0,[z0,z1,z3,z4,z896,z6]),(0,[z0,z1,z3,z4,z5,z897]),(0,[z1,z3,z4,z51,z6,z375]),(0,[z0,z141,z3,z4,z5,z6]),(0,[z583,z0,z3,z4,z55,z6]),(0,[z0,z280,z3,z4,z55,z6]),(0,[z0,z1,z58,z103,z52,z6]),(0,[z169,z0,z3,z4,z422,z6])]],
   [[(0,[z0,z1,z3,z4,z898,z6]),(0,[z17,z0,z3,z172,z5,z6]),(0,[z1,z3,z130,z157,z5,z6]),(0,[z0,z1,z3,z21,z6,z310]),(0,[z0,z1,z3,z4,z899,z6]),(0,[z0,z1,z3,z4,z900,z6]),(0,[z0,z40,z3,z140,z55,z6]),(0,[z0,z1,z4,z901,z5,z6])],[(0,[z0,z1,z3,z4,z144,z6]),(0,[z30,z0,z3,z4,z85,z6]),(0,[z0,z3,z77,z140,z55,z6]),(0,[z0,z1,z3,z4,z902,z6]),(0,[z711,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z903,z6,z13])],[(0,[z15,z1,z16,z4,z51,z6]),(0,[z0,z1,z3,z335,z52,z6]),(0,[z0,z1,z3,z4,z904,z6]),(0,[z0,z3,z4,z23,z51,z6]),(0,[z173,z1,z3,z31,z5,z6]),(0,[z0,z1,z3,z4,z905,z6]),(0,[z1,z3,z4,z5,z6,z906]),(0,[z0,z1,z3,z67,z94,z6]),(0,[z1,z45,z3,z5,z13,z14])],[(0,[z0,z1,z3,z907,z5,z6]),(0,[z0,z11,z3,z501,z4,z6]),(0,[z0,z1,z3,z4,z908,z6]),(0,[z135,z1,z3,z4,z775,z6])],[(0,[z0,z1,z3,z4,z909,z6]),(0,[z0,z1,z3,z4,z910,z6]),(0,[z1,z3,z4,z604,z21,z6]),(0,[z0,z1,z3,z911,z5,z6]),(0,[z0,z912,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z913,z6]),(0,[z0,z1,z3,z4,z914,z6]),(0,[z548,z1,z3,z4,z53,z6]),(0,[z915,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z916,z6]),(0,[z1,z3,z4,z21,z156,z6]),(0,[z0,z1,z3,z917,z4,z21]),(0,[z0,z93,z3,z4,z55,z6]),(0,[z918,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z10,z55,z42]),(0,[z0,z3,z4,z55,z6,z38]),(0,[z1,z3,z4,z772,z103,z6]),(0,[z919,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z920,z6])],[(0,[z0,z3,z4,z140,z85,z6]),(0,[z0,z90,z3,z4,z257,z6]),(0,[z89,z1,z3,z4,z434,z6]),(0,[z0,z3,z4,z596,z55,z6]),(0,[z0,z921,z3,z4,z23,z6]),(0,[z0,z1,z3,z4,z922,z6]),(0,[z1,z3,z202,z4,z604,z6])],[(0,[z0,z1,z3,z149,z51,z6]),(0,[z63,z1,z3,z77,z21,z6]),(0,[z0,z3,z4,z52,z359,z6]),(0,[z1,z3,z4,z5,z6,z923]),(0,[z0,z1,z3,z4,z924,z6]),(0,[z0,z1,z3,z202,z4,z295])]],
   [[(0,[z925,z1,z3,z4,z5,z6]),(0,[z0,z456,z3,z4,z52,z6]),(0,[z84,z411,z3,z4,z5,z6])],[(0,[z82,z1,z3,z4,z5,z6]),(0,[z30,z173,z3,z4,z55,z6]),(0,[z518,z1,z3,z140,z5,z6]),(0,[z0,z1,z3,z4,z926,z6]),(0,[z97,z0,z3,z4,z5,z42]),(0,[z0,z3,z298,z4,z6,z177])],[(0,[z0,z1,z3,z4,z927,z6]),(0,[z0,z1,z3,z4,z928,z6]),(0,[z0,z1,z3,z4,z359,z6]),(0,[z18,z90,z3,z4,z21,z6]),(0,[z0,z1,z3,z929,z5,z6]),(0,[z89,z1,z3,z157,z5,z101]),(0,[z930,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z931,z6]),(0,[z1,z3,z67,z462,z94,z6])],[(1,[z48,z3,z76,z5,z6]),(0,[z0,z1,z3,z76,z51,z6]),(0,[z0,z1,z932,z4,z5,z6]),(0,[z0,z1,z3,z4,z933,z6]),(0,[z0,z1,z3,z5,z6,z934]),(0,[z0,z1,z3,z4,z5,z935]),(0,[z0,z1,z400,z4,z546,z6]),(0,[z243,z0,z1,z4,z55,z36]),(0,[z0,z936,z3,z4,z5,z6])],[(0,[z129,z1,z3,z4,z144,z6]),(0,[z1,z3,z4,z144,z49,z6]),(0,[z0,z1,z3,z937,z5,z6]),(0,[z84,z1,z3,z4,z21,z6]),(0,[z81,z1,z3,z4,z51,z6]),(0,[z0,z1,z938,z3,z4,z6]),(0,[z0,z1,z3,z394,z52,z6]),(0,[z743,z1,z3,z4,z5,z6])],[(0,[z0,z3,z205,z5,z55,z6]),(0,[z0,z1,z3,z4,z56,z499])],[(0,[z0,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z939,z6]),(0,[z0,z90,z3,z4,z51,z6]),(0,[z91,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z940,z6]),(0,[z0,z1,z3,z4,z941,z6])],[(0,[z0,z1,z3,z76,z319,z6]),(0,[z0,z1,z3,z4,z5,z942]),(0,[z0,z211,z3,z4,z55,z6]),(0,[z518,z1,z3,z4,z21,z6]),(0,[z135,z1,z3,z4,z21,z6]),(0,[z943,z1,z3,z4,z5,z6]),(0,[z944,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z191,z5,z6]),(0,[z0,z3,z4,z52,z945,z6]),(0,[z1,z3,z946,z4,z52,z6])]],
   [[(0,[z0,z1,z947,z3,z5,z6]),(0,[z1,z3,z4,z21,z6,z387]),(0,[z0,z1,z3,z409,z438,z6]),(0,[z30,z0,z147,z4,z51,z6]),(0,[z0,z1,z948,z3,z4,z6]),(0,[z0,z1,z3,z4,z949,z6]),(0,[z0,z1,z3,z4,z950,z6]),(0,[z0,z3,z4,z140,z366,z6]),(0,[z0,z1,z3,z4,z951,z6]),(0,[z0,z1,z58,z218,z103,z6]),(0,[z0,z1,z3,z4,z952,z6]),(0,[z0,z1,z3,z4,z5,z953])],[(0,[z198,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z149,z100,z6]),(0,[z0,z1,z3,z4,z747,z6]),(0,[z0,z41,z3,z4,z5,z439]),(0,[z254,z0,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z200,z6]),(0,[z3,z4,z5,z6,z177,z375]),(0,[z954,z0,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z955,z6]),(0,[z0,z956,z3,z4,z5,z6]),(0,[z0,z1,z3,z157,z21,z6]),(0,[z0,z1,z336,z4,z481,z6]),(0,[z0,z3,z4,z140,z293,z6]),(0,[z0,z1,z3,z4,z945,z6])],[(0,[z63,z1,z3,z77,z51,z6]),(0,[z0,z1,z3,z4,z274,z6]),(0,[z957,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z958,z6]),(0,[z0,z45,z3,z140,z55,z6]),(0,[z0,z3,z501,z4,z55,z6]),(0,[z0,z1,z3,z4,z5,z959]),(0,[z82,z1,z3,z4,z799,z6]),(0,[z0,z1,z3,z784,z5,z6]),(0,[z0,z1,z3,z960,z5,z6])],[(0,[z26,z48,z3,z4,z55,z6]),(0,[z0,z1,z3,z961,z4,z6]),(0,[z0,z428,z3,z4,z962,z6]),(0,[z0,z1,z3,z4,z5,z963]),(0,[z0,z1,z3,z4,z964,z6]),(0,[z0,z98,z3,z4,z381,z6]),(0,[z965,z1,z3,z4,z5,z6]),(0,[z383,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z202,z4,z339]),(0,[z0,z1,z3,z5,z751,z14]),(0,[z1,z3,z4,z604,z12,z6])],[(0,[z0,z1,z3,z966,z5,z6]),(0,[z1,z666,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z967,z5]),(0,[z0,z1,z3,z968,z5,z6]),(0,[z669,z1,z3,z4,z21,z6]),(0,[z1,z3,z4,z185,z51,z6]),(0,[z1,z3,z4,z899,z6,z375]),(0,[z0,z1,z3,z4,z969,z6])],[(0,[z89,z1,z3,z251,z21,z6]),(0,[z173,z1,z3,z4,z21,z6]),(0,[z0,z428,z336,z4,z5,z6]),(0,[z81,z1,z3,z205,z5,z6]),(0,[z0,z1,z3,z4,z970,z6]),(0,[z0,z1,z58,z152,z5,z6])],[(0,[z0,z1,z3,z4,z971,z6]),(0,[z0,z3,z4,z5,z55,z439]),(0,[z0,z627,z3,z4,z55,z6])]],
   [[(0,[z15,z1,z752,z4,z5,z6]),(0,[z0,z1,z3,z4,z972,z6]),(0,[z81,z1,z3,z4,z873,z6]),(0,[z0,z41,z3,z4,z52,z6]),(0,[z0,z3,z346,z4,z5,z6]),(0,[z1,z3,z4,z5,z6,z973])],[(0,[z0,z1,z3,z4,z974,z6]),(0,[z89,z1,z3,z4,z5,z467]),(0,[z1,z3,z4,z77,z328,z6]),(0,[z0,z1,z3,z4,z975,z6]),(0,[z1,z3,z680,z4,z21,z6]),(0,[z0,z141,z3,z4,z51,z6]),(0,[z0,z146,z3,z4,z949,z6]),(0,[z976,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z977,z6]),(0,[z1,z3,z978,z4,z5,z6]),(0,[z0,z3,z979,z4,z5,z6])],[(0,[z18,z1,z74,z4,z21,z6]),(0,[z368,z1,z3,z4,z21,z6]),(0,[z0,z1,z980,z4,z5,z6]),(0,[z1,z3,z4,z543,z21,z6]),(0,[z0,z1,z3,z4,z6,z981])],[(0,[z0,z1,z3,z982,z5,z6]),(0,[z0,z1,z3,z4,z983,z6]),(0,[z0,z64,z3,z4,z984,z6]),(0,[z138,z1,z3,z4,z21,z6]),(0,[z181,z1,z3,z4,z21,z6]),(0,[z367,z1,z336,z4,z5,z6]),(1,[z1,z3,z4,z772,z6]),(0,[z135,z1,z3,z4,z311,z6])],[(0,[z70,z1,z3,z77,z5,z6]),(0,[z1,z3,z4,z829,z21,z6]),(0,[z1,z3,z661,z4,z51,z6]),(0,[z198,z1,z3,z4,z259,z6]),(0,[z65,z0,z3,z771,z5,z6]),(0,[z0,z40,z3,z4,z985,z6]),(0,[z0,z3,z638,z4,z55,z6]),(0,[z0,z1,z986,z3,z4,z6]),(0,[z0,z987,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z988,z6]),(0,[z0,z64,z3,z4,z164,z6]),(0,[z1,z3,z4,z21,z431,z6]),(0,[z0,z1,z3,z989,z5,z6]),(0,[z990,z1,z3,z4,z5,z6]),(0,[z169,z0,z218,z3,z4,z6]),(0,[z0,z3,z991,z4,z5,z6])],[(0,[z0,z1,z3,z4,z992,z6]),(0,[z0,z1,z3,z4,z993,z6]),(0,[z0,z1,z3,z4,z994,z6]),(0,[z0,z3,z4,z293,z6,z42])],[(0,[z0,z1,z3,z4,z995,z6]),(0,[z0,z211,z3,z4,z434,z6]),(0,[z0,z996,z3,z4,z5,z6]),(0,[z1,z3,z4,z77,z53,z6]),(0,[z0,z1,z3,z4,z997,z6]),(0,[z0,z1,z3,z31,z21,z6]),(0,[z0,z1,z3,z4,z998,z6]),(0,[z999,z1,z3,z4,z5,z6]),(0,[z0,z1000,z3,z4,z5,z6])]],
   [[(0,[z0,z1001,z3,z4,z5,z6]),(0,[z0,z1,z3,z251,z5,z6]),(0,[z0,z1,z3,z4,z1002,z6])],[(0,[z1,z72,z3,z4,z5,z6]),(0,[z0,z411,z3,z4,z5,z6])],[(0,[z0,z1,z3,z1003,z5,z6]),(0,[z15,z1,z16,z4,z55,z6]),(0,[z173,z1,z3,z4,z51,z6]),(0,[z0,z98,z3,z4,z263,z6]),(0,[z0,z649,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z259,z6]),(0,[z0,z3,z4,z23,z55,z6])],[(0,[z0,z1,z3,z4,z5,z1004]),(0,[z89,z1,z3,z4,z85,z6]),(0,[z84,z1,z3,z4,z341,z6]),(0,[z0,z3,z754,z4,z21,z6]),(0,[z97,z0,z3,z4,z51,z42]),(0,[z82,z1,z3,z4,z51,z6]),(0,[z30,z0,z3,z4,z381,z6]),(0,[z0,z1,z3,z4,z1005,z6]),(0,[z0,z11,z3,z4,z596,z6]),(0,[z0,z1,z125,z3,z298,z6])],[(0,[z48,z3,z4,z76,z5,z6]),(0,[z0,z1,z3,z4,z1006,z6]),(0,[z0,z3,z4,z1007,z5,z6])],[(0,[z0,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z1008,z5,z6]),(0,[z0,z1,z3,z4,z824,z6]),(0,[z474,z1,z3,z4,z21,z6]),(0,[z0,z537,z3,z4,z55,z6]),(0,[z1009,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1010,z6]),(0,[z0,z1,z3,z172,z19,z6]),(0,[z0,z1,z1011,z4,z5,z6]),(0,[z0,z1,z3,z4,z1012,z6]),(0,[z89,z1,z3,z251,z5,z101]),(0,[z0,z1,z3,z1013,z5,z6]),(0,[z1014,z1,z3,z4,z5,z6]),(0,[z65,z0,z3,z140,z52,z6]),(0,[z0,z57,z3,z394,z55,z6]),(0,[z0,z1,z3,z4,z1015,z6])],[(0,[z0,z1,z3,z1016,z4,z6]),(0,[z30,z0,z3,z4,z1017,z6]),(0,[z0,z225,z98,z4,z55,z6]),(0,[z1,z3,z4,z5,z6,z1018]),(0,[z135,z1,z45,z3,z5,z14])]],
   [[(0,[z1,z3,z16,z4,z144,z6]),(0,[z0,z1,z3,z4,z1019,z6]),(0,[z0,z1,z3,z4,z5,z1020]),(0,[z0,z1,z3,z4,z1021,z6]),(0,[z1,z3,z4,z19,z21,z6]),(0,[z0,z1,z3,z1022,z4,z6]),(0,[z0,z1,z3,z150,z96,z6]),(0,[z169,z0,z3,z4,z5,z6])],[(0,[z0,z1,z1023,z4,z5,z6]),(1,[z1,z3,z172,z21,z6]),(0,[z89,z1,z3,z4,z21,z49]),(0,[z1,z3,z157,z5,z21,z6]),(0,[z0,z1,z3,z191,z51,z6]),(0,[z0,z146,z3,z251,z5,z6]),(0,[z317,z1,z3,z4,z481,z6]),(0,[z0,z1,z3,z5,z6,z1024]),(0,[z0,z40,z3,z20,z55,z6]),(0,[z0,z3,z1025,z4,z5,z6]),(0,[z0,z3,z4,z714,z5,z6])],[(0,[z0,z1,z3,z4,z1026,z6]),(0,[z1,z3,z516,z4,z21,z49]),(0,[z82,z1,z3,z4,z864,z6])],[(0,[z0,z1,z3,z1027,z5,z6]),(0,[z0,z1,z3,z76,z55,z6]),(0,[z0,z1,z3,z4,z1028,z6]),(0,[z26,z48,z3,z4,z21,z6]),(0,[z89,z1,z3,z4,z21,z101]),(0,[z383,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z31,z51,z6]),(0,[z198,z1,z3,z4,z51,z6]),(0,[z30,z173,z147,z4,z5,z6]),(0,[z0,z1,z3,z4,z1029,z6]),(0,[z0,z1,z3,z4,z1030,z6]),(0,[z0,z1,z3,z202,z4,z953])],[(0,[z1,z3,z16,z4,z328,z6]),(0,[z0,z64,z3,z4,z52,z6]),(0,[z1,z3,z4,z51,z6,z13]),(0,[z81,z1,z3,z4,z55,z6]),(0,[z173,z1,z3,z205,z5,z6]),(0,[z57,z82,z3,z4,z55,z6]),(0,[z1031,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1032,z6]),(0,[z0,z1,z1033,z3,z4,z6]),(0,[z0,z3,z346,z4,z276,z6]),(0,[z0,z3,z4,z5,z1034,z6])],[(0,[z0,z1,z3,z1035,z5,z6]),(0,[z0,z1,z3,z4,z1036,z6]),(0,[z0,z1,z336,z4,z52,z6]),(0,[z0,z3,z4,z55,z652,z6]),(1,[z0,z3,z191,z55,z6]),(0,[z1,z1037,z3,z4,z5,z6])],[(0,[z1,z16,z4,z21,z6,z36]),(0,[z0,z146,z3,z4,z21,z6]),(0,[z0,z3,z176,z140,z5,z6]),(0,[z91,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z1038,z5,z6]),(0,[z0,z1,z4,z1039,z5,z6]),(0,[z1,z125,z3,z5,z6,z375])],[(0,[z17,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1040,z6]),(0,[z1041,z1,z3,z4,z5,z6]),(0,[z518,z1,z3,z4,z366,z6]),(0,[z0,z3,z4,z5,z6,z959]),(0,[z91,z1,z3,z191,z5,z6]),(0,[z1,z3,z1042,z4,z6,z375])]],
   [[(0,[z0,z3,z4,z249,z359,z6]),(0,[z0,z1,z3,z4,z1043,z6]),(0,[z129,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z728,z6]),(0,[z0,z1,z3,z4,z1044,z6]),(0,[z0,z1,z3,z1045,z5,z6]),(0,[z0,z1046,z3,z4,z5,z6]),(0,[z0,z1,z1047,z4,z5,z6]),(0,[z0,z1,z3,z4,z1048,z6]),(0,[z1,z3,z462,z4,z52,z6]),(0,[z0,z3,z4,z1049,z5,z6]),(0,[z0,z1,z3,z202,z4,z402]),(0,[z367,z1,z125,z3,z5,z6])],[(0,[z0,z1,z3,z4,z1050,z6]),(0,[z17,z18,z3,z4,z21,z6]),(0,[z1,z58,z3,z77,z21,z6]),(0,[z30,z0,z3,z4,z263,z6]),(0,[z0,z1,z3,z4,z1051,z6]),(0,[z0,z1,z3,z4,z1052,z6]),(0,[z0,z1,z400,z4,z34,z6]),(0,[z91,z1,z3,z4,z200,z6]),(0,[z1,z3,z4,z422,z772,z6]),(0,[z0,z1,z3,z5,z6,z310]),(0,[z0,z1,z3,z4,z311,z6])],[(0,[z0,z48,z3,z4,z5,z439]),(0,[z1,z3,z4,z21,z307,z6]),(0,[z135,z1,z3,z130,z5,z6]),(0,[z0,z3,z346,z4,z51,z6]),(0,[z518,z98,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1053,z6]),(0,[z518,z1,z3,z20,z5,z6]),(0,[z1054,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1055,z6]),(0,[z63,z1,z3,z77,z55,z6]),(1,[z1,z336,z4,z21,z6]),(0,[z1,z3,z4,z293,z21,z6]),(0,[z0,z1,z3,z4,z903,z6]),(0,[z30,z0,z147,z31,z5,z6]),(0,[z0,z1,z3,z4,z1056,z6]),(0,[z1057,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1058,z6])],[(0,[z0,z1,z3,z4,z419,z6]),(0,[z0,z1,z3,z4,z1059,z6]),(0,[z0,z3,z4,z250,z55,z6]),(0,[z0,z1,z3,z4,z56,z6]),(0,[z0,z1,z1060,z4,z5,z6])],[(0,[z0,z1,z1061,z4,z5,z6])],[(0,[z0,z1,z3,z4,z5,z1062]),(0,[z0,z1,z3,z4,z1063,z6]),(0,[z236,z0,z3,z4,z5,z6])],[(0,[z0,z1,z414,z4,z5,z6]),(0,[z0,z1064,z3,z4,z5,z6]),(0,[z1,z3,z4,z1065,z21,z6]),(0,[z89,z211,z3,z4,z5,z6]),(0,[z1066,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z176,z94,z6]),(0,[z0,z1,z1067,z3,z4,z6])]],
   [[(0,[z0,z3,z4,z1068,z5,z6]),(0,[z0,z3,z4,z55,z6,z679]),(0,[z173,z1,z3,z4,z1069,z6]),(0,[z84,z1,z3,z4,z55,z6])],[(0,[z0,z1,z3,z1070,z5,z6]),(0,[z0,z3,z4,z23,z21,z6]),(0,[z89,z1,z3,z4,z5,z719]),(0,[z0,z1,z3,z4,z1071,z6]),(0,[z0,z1,z58,z784,z5,z6]),(0,[z236,z0,z3,z298,z4,z6]),(0,[z0,z1,z3,z1072,z4,z6]),(0,[z1073,z1,z3,z4,z5,z6]),(0,[z1074,z1,z3,z4,z5,z6])],[(0,[z1,z3,z16,z4,z192,z6]),(0,[z0,z1,z3,z4,z1075,z6]),(0,[z0,z1,z3,z4,z1076,z6]),(0,[z0,z1,z3,z251,z51,z6]),(0,[z0,z1,z3,z4,z1077,z6]),(0,[z0,z1,z3,z4,z1078,z6])],[(0,[z0,z428,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z85,z6]),(0,[z1,z72,z3,z4,z51,z6]),(0,[z0,z411,z3,z4,z51,z6]),(0,[z0,z1,z414,z4,z52,z6]),(0,[z0,z1,z3,z205,z5,z6]),(0,[z0,z57,z3,z4,z793,z6]),(0,[z0,z3,z4,z55,z246,z6]),(0,[z135,z1,z3,z4,z55,z6]),(0,[z0,z3,z346,z67,z4,z6])],[(0,[z0,z1,z3,z4,z341,z6]),(0,[z1,z615,z3,z4,z21,z6]),(0,[z30,z81,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z1079,z6]),(0,[z1080,z1,z3,z4,z5,z6]),(0,[z1081,z1,z3,z4,z5,z6])],[(0,[z95,z0,z3,z76,z5,z6]),(0,[z0,z1,z3,z1082,z5,z6]),(0,[z0,z1,z3,z4,z1083,z6]),(0,[z0,z1,z1084,z3,z4,z6]),(0,[z1085,z1,z3,z4,z5,z6]),(0,[z0,z3,z4,z887,z23,z6]),(0,[z1,z3,z1086,z4,z5,z6]),(0,[z0,z3,z4,z5,z6,z1087]),(0,[z135,z1,z3,z4,z1088,z6]),(0,[z0,z1,z3,z4,z714,z6])],[(0,[z0,z1,z3,z149,z21,z6]),(0,[z0,z3,z8,z4,z55,z6]),(0,[z0,z1089,z3,z4,z5,z6]),(0,[z0,z283,z3,z4,z55,z6]),(0,[z0,z1,z3,z157,z55,z6]),(0,[z0,z1,z3,z4,z1090,z6]),(0,[z0,z1,z3,z1091,z5,z6]),(0,[z0,z3,z4,z55,z262,z6]),(0,[z1092,z1,z3,z4,z5,z6]),(0,[z0,z1,z58,z103,z5,z6]),(0,[z0,z1,z125,z3,z372,z6])],[(0,[z0,z1,z3,z4,z5,z1093]),(0,[z0,z1094,z3,z4,z5,z6]),(0,[z0,z1,z1095,z4,z5,z6]),(0,[z0,z1,z3,z4,z829,z6]),(0,[z0,z1,z3,z4,z1096,z6]),(0,[z0,z1,z3,z4,z1097,z6]),(0,[z0,z1,z3,z1098,z4,z6]),(0,[z169,z1099,z3,z4,z5,z6]),(0,[z1,z72,z3,z4,z12,z6]),(0,[z243,z0,z1,z5,z310,z36])]],
   [[(0,[z668,z48,z3,z4,z5,z6]),(0,[z1,z3,z4,z21,z348,z6])],[(0,[z26,z48,z3,z4,z85,z6]),(0,[z0,z1,z3,z335,z5,z6]),(0,[z0,z1,z3,z4,z1100,z6]),(0,[z0,z1,z3,z4,z1101,z6]),(0,[z0,z1,z3,z4,z1102,z6]),(0,[z0,z1,z3,z4,z116,z439]),(0,[z0,z1,z1103,z4,z5,z6]),(0,[z1104,z1,z3,z4,z52,z6])],[(0,[z0,z1,z3,z1105,z5,z6]),(0,[z0,z1,z3,z4,z1106,z6]),(0,[z169,z0,z3,z4,z51,z6]),(0,[z173,z1,z3,z4,z55,z6]),(0,[z30,z0,z885,z4,z5,z6]),(0,[z0,z1,z3,z4,z1107,z6]),(0,[z1,z3,z4,z5,z6,z1108]),(0,[z0,z68,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z356,z6]),(0,[z0,z1,z125,z3,z52,z6]),(0,[z0,z1,z3,z4,z1109,z6]),(0,[z0,z3,z1110,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1111,z6]),(0,[z18,z1,z3,z4,z85,z6]),(0,[z1,z48,z3,z4,z293,z6]),(0,[z0,z1,z3,z4,z1112,z6]),(0,[z0,z1,z3,z4,z1113,z6]),(0,[z63,z1,z3,z77,z434,z6]),(0,[z81,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z5,z1114]),(0,[z82,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z176,z550,z6]),(0,[z0,z1,z3,z4,z1115,z6])],[(0,[z770,z0,z3,z4,z5,z6]),(0,[z367,z1,z3,z4,z52,z6]),(0,[z317,z1,z3,z4,z52,z6]),(0,[z82,z1,z3,z191,z5,z6]),(0,[z1,z72,z3,z67,z4,z6]),(0,[z243,z367,z1,z4,z5,z36]),(0,[z1116,z1,z3,z4,z5,z6]),(0,[z0,z1,z1117,z3,z4,z6])],[(0,[z0,z90,z3,z4,z21,z6]),(0,[z91,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z880,z21]),(0,[z0,z41,z3,z4,z328,z6]),(0,[z0,z1,z3,z4,z1118,z6]),(0,[z0,z1,z3,z4,z366,z6]),(0,[z1,z3,z4,z5,z6,z1119])],[(0,[z0,z1,z3,z4,z1120,z6]),(0,[z0,z3,z863,z4,z21,z6]),(0,[z82,z1,z3,z4,z200,z6]),(0,[z243,z1,z4,z5,z375,z36])],[(0,[z0,z1,z3,z4,z293,z6]),(0,[z369,z1,z3,z4,z21,z6]),(0,[z30,z0,z147,z4,z21,z6]),(0,[z1,z166,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z1121,z6]),(0,[z0,z3,z4,z838,z51,z6]),(0,[z0,z1,z3,z4,z1069,z6]),(0,[z0,z1,z3,z4,z183,z6]),(0,[z621,z0,z3,z4,z55,z6]),(0,[z435,z0,z3,z4,z55,z6]),(0,[z135,z1,z3,z4,z423,z6])]],
   [[(0,[z0,z57,z3,z4,z292,z6]),(0,[z1,z3,z634,z4,z21,z6]),(0,[z0,z1,z3,z4,z324,z6]),(0,[z0,z1,z267,z4,z329,z6]),(0,[z0,z1,z3,z4,z1122,z6])],[(0,[z0,z211,z3,z130,z5,z6]),(0,[z322,z1,z3,z4,z21,z6]),(0,[z0,z428,z3,z4,z821,z6]),(0,[z0,z1,z414,z4,z415,z6]),(0,[z0,z1,z3,z726,z5,z6]),(0,[z0,z1,z3,z191,z55,z6]),(0,[z0,z458,z3,z4,z52,z6])],[(0,[z18,z1,z3,z4,z53,z6]),(0,[z0,z1,z3,z4,z1123,z6]),(0,[z0,z424,z3,z4,z55,z6]),(0,[z0,z3,z4,z596,z52,z6]),(0,[z0,z1124,z3,z4,z5,z6]),(0,[z243,z236,z0,z4,z5,z36])],[(0,[z0,z1,z3,z4,z1125,z6]),(0,[z0,z1,z3,z4,z1126,z6]),(0,[z0,z1,z3,z4,z1127,z6]),(0,[z0,z1,z45,z3,z21,z14]),(0,[z0,z1,z3,z4,z5,z439]),(0,[z0,z1,z3,z31,z55,z6]),(0,[z30,z0,z3,z4,z55,z439]),(0,[z198,z1,z3,z4,z55,z6]),(0,[z0,z1,z3,z394,z5,z6])],[(0,[z454,z48,z3,z4,z5,z6]),(0,[z1,z3,z16,z4,z21,z6]),(0,[z1,z3,z409,z77,z5,z6]),(0,[z0,z597,z3,z4,z52,z6]),(0,[z0,z1,z3,z409,z94,z6]),(0,[z0,z1,z3,z191,z200,z6])],[(0,[z0,z1128,z3,z4,z5,z6]),(0,[z63,z64,z3,z77,z5,z6]),(0,[z1,z3,z4,z51,z21,z6]),(0,[z1,z3,z4,z21,z6,z375]),(0,[z0,z428,z3,z4,z415,z6]),(0,[z0,z41,z3,z4,z116,z6]),(0,[z0,z1,z3,z733,z5,z6]),(0,[z1129,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1130,z6])],[(0,[z0,z1,z3,z149,z319,z6]),(0,[z0,z40,z3,z4,z292,z6]),(0,[z0,z3,z850,z4,z51,z6]),(0,[z1,z3,z946,z4,z5,z6]),(0,[z0,z3,z4,z52,z55,z6]),(0,[z0,z1,z3,z4,z1131,z6])],[(0,[z0,z1,z3,z4,z1132,z6]),(0,[z0,z1,z3,z4,z1133,z6]),(0,[z0,z853,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z52,z439]),(0,[z1134,z1,z3,z4,z5,z6]),(0,[z243,z0,z1,z4,z52,z36]),(0,[z0,z1,z3,z4,z5,z766])]],
   [[(0,[z1,z3,z195,z4,z21,z6]),(0,[z0,z141,z3,z4,z21,z6]),(0,[z236,z0,z3,z4,z51,z6]),(0,[z0,z107,z3,z4,z55,z6]),(0,[z0,z502,z3,z4,z55,z6]),(0,[z0,z3,z4,z55,z80,z6]),(0,[z0,z1,z3,z4,z5,z1135]),(0,[z0,z1,z3,z4,z1136,z6]),(0,[z0,z1,z3,z4,z1137,z6])],[(0,[z95,z0,z3,z4,z328,z6]),(0,[z0,z1,z3,z4,z1065,z6]),(0,[z0,z1,z3,z4,z1138,z6]),(0,[z0,z1,z3,z4,z1139,z6]),(0,[z0,z3,z1140,z4,z5,z6]),(0,[z0,z1141,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1142,z6]),(0,[z0,z1,z3,z4,z5,z719]),(0,[z0,z3,z4,z372,z6,z177]),(0,[z135,z1143,z3,z4,z5,z6])],[(0,[z208,z0,z3,z4,z328,z6]),(0,[z81,z1,z3,z4,z56,z6]),(0,[z0,z3,z4,z116,z55,z6]),(0,[z0,z119,z3,z4,z55,z6])],[(0,[z153,z1,z3,z4,z293,z6]),(0,[z0,z1,z3,z4,z1144,z6]),(0,[z0,z1,z3,z335,z257,z6]),(0,[z0,z1,z3,z1145,z5,z6]),(0,[z0,z211,z3,z4,z52,z6]),(0,[z1,z3,z4,z21,z386,z6]),(0,[z1146,z1,z3,z4,z5,z6]),(0,[z1,z72,z3,z4,z34,z6]),(0,[z0,z1,z3,z5,z6,z1147]),(0,[z0,z1,z3,z4,z1088,z6])],[(0,[z26,z48,z3,z4,z249,z6]),(0,[z0,z1,z3,z4,z1148,z6]),(0,[z1,z3,z4,z777,z55,z6]),(0,[z0,z1,z3,z1149,z5,z6])],[(0,[z0,z1,z3,z1150,z5,z6]),(0,[z0,z1,z3,z4,z19,z6]),(0,[z18,z1,z16,z4,z21,z6]),(0,[z0,z1,z3,z4,z1151,z6]),(0,[z0,z1,z3,z4,z1152,z6]),(0,[z0,z1,z3,z911,z21,z6]),(0,[z0,z1,z3,z205,z51,z6]),(0,[z0,z1,z3,z4,z1153,z6]),(0,[z0,z1,z3,z4,z1154,z6]),(0,[z0,z3,z4,z1005,z6,z177]),(0,[z0,z3,z202,z501,z4,z6])],[(0,[z0,z1,z3,z1155,z5,z6]),(0,[z0,z1,z3,z1156,z5,z6]),(0,[z1,z3,z4,z5,z6,z1157]),(0,[z0,z1,z1158,z3,z5,z6]),(0,[z0,z3,z4,z771,z5,z6]),(0,[z0,z3,z332,z4,z55,z42]),(0,[z0,z1,z3,z4,z1159,z6])],[(0,[z18,z1,z3,z335,z21,z6]),(0,[z0,z1,z45,z3,z51,z14]),(0,[z89,z1,z3,z4,z55,z101]),(0,[z0,z3,z501,z4,z52,z6]),(0,[z367,z1,z3,z4,z1160,z6]),(0,[z0,z1,z45,z3,z311,z14])]],
   [[(0,[z0,z1,z3,z4,z1161,z6]),(0,[z1,z3,z4,z77,z144,z6]),(0,[z0,z1,z58,z103,z51,z6]),(0,[z0,z1,z3,z4,z1162,z6]),(0,[z0,z1,z3,z4,z168,z6]),(0,[z0,z148,z3,z4,z55,z6]),(0,[z0,z3,z4,z381,z6,z42]),(0,[z0,z1,z3,z4,z1163,z6]),(0,[z0,z1164,z3,z4,z5,z6]),(0,[z1165,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z953,z221])],[(0,[z0,z1,z1166,z3,z4,z6]),(0,[z18,z1,z3,z4,z1065,z6]),(0,[z0,z1,z3,z4,z1167,z6]),(1,[z0,z3,z205,z55,z6]),(0,[z1,z3,z4,z52,z6,z13]),(0,[z1,z3,z4,z1168,z52,z6])],[(0,[z97,z0,z3,z4,z21,z42]),(0,[z82,z1,z3,z4,z21,z6]),(0,[z0,z146,z3,z4,z55,z6]),(0,[z0,z1,z3,z251,z55,z6]),(0,[z1099,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z335,z51,z6]),(0,[z383,z1,z3,z4,z19,z6]),(0,[z0,z1,z3,z4,z1169,z6]),(0,[z91,z428,z3,z4,z5,z6]),(0,[z0,z424,z3,z140,z5,z6]),(0,[z102,z0,z3,z4,z945,z6]),(0,[z1,z72,z3,z4,z55,z6])],[(0,[z0,z1,z3,z4,z1170,z6]),(0,[z0,z1,z3,z4,z5,z1171]),(0,[z888,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z372,z6,z310])],[(0,[z770,z26,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1172,z6]),(0,[z162,z1,z3,z172,z5,z6]),(0,[z211,z3,z4,z77,z5,z6]),(0,[z0,z1,z3,z4,z1173,z6]),(0,[z30,z0,z147,z205,z5,z6]),(0,[z0,z3,z4,z5,z959,z42]),(0,[z1,z72,z3,z4,z158,z6]),(0,[z236,z3,z4,z5,z6,z375]),(0,[z0,z1,z3,z4,z423,z6])],[(0,[z0,z1,z3,z4,z1174,z6]),(0,[z0,z1,z3,z4,z1175,z6]),(0,[z0,z98,z3,z4,z292,z6]),(0,[z30,z81,z147,z4,z5,z6]),(0,[z0,z1,z3,z4,z1176,z6])],[(0,[z0,z1,z3,z21,z6,z1177]),(0,[z0,z1,z3,z4,z1178,z6]),(0,[z0,z1,z3,z4,z1179,z6]),(0,[z0,z1,z3,z67,z547,z6])]],
   [[(0,[z0,z1,z3,z191,z21,z6]),(0,[z1,z3,z4,z21,z6,z432]),(0,[z1,z3,z4,z481,z21,z6]),(0,[z0,z1,z3,z4,z116,z499]),(0,[z0,z1,z3,z4,z1180,z6]),(0,[z0,z1181,z3,z4,z5,z6]),(0,[z243,z0,z4,z5,z177,z36])],[(0,[z0,z1,z3,z4,z1182,z6]),(0,[z0,z90,z3,z335,z5,z6]),(0,[z0,z1,z3,z4,z434,z6]),(0,[z0,z1,z1183,z4,z5,z6]),(0,[z0,z1,z3,z1184,z5,z6]),(0,[z0,z1,z3,z4,z1017,z6]),(0,[z0,z1,z3,z1185,z5,z6]),(0,[z0,z3,z4,z5,z945,z6]),(0,[z0,z3,z4,z55,z88,z6]),(0,[z0,z3,z4,z793,z55,z6]),(0,[z0,z1,z3,z271,z88,z6]),(0,[z1,z3,z298,z4,z6,z375]),(0,[z0,z1,z3,z1186,z5,z6])],[(0,[z198,z1,z3,z4,z21,z6]),(0,[z0,z3,z4,z183,z55,z6]),(0,[z91,z1,z3,z4,z356,z6]),(0,[z0,z1,z3,z844,z67,z6])],[(0,[z0,z1,z3,z4,z1187,z6])],[(0,[z0,z1,z3,z4,z1188,z6]),(0,[z17,z173,z3,z4,z5,z6]),(0,[z632,z1,z3,z4,z21,z6]),(0,[z1,z336,z4,z5,z21,z6]),(0,[z0,z304,z3,z4,z52,z6]),(0,[z1,z3,z4,z5,z6,z1189])],[(0,[z1,z3,z4,z192,z49,z6]),(0,[z0,z1,z3,z1190,z5,z6]),(0,[z0,z1,z3,z4,z1191,z6]),(0,[z65,z0,z3,z140,z5,z6]),(0,[z0,z1,z3,z4,z1192,z6]),(0,[z0,z1,z3,z4,z1193,z6]),(0,[z0,z1,z3,z4,z1160,z6])],[(0,[z0,z1,z3,z172,z52,z6]),(0,[z0,z3,z885,z4,z5,z6]),(0,[z0,z98,z4,z500,z55,z6]),(0,[z0,z3,z4,z55,z6,z170]),(0,[z0,z1,z3,z4,z1194,z6]),(0,[z243,z0,z1,z125,z5,z36])],[(0,[z0,z1,z3,z1195,z5,z6]),(0,[z1,z187,z16,z4,z5,z6]),(0,[z0,z1,z3,z4,z1196,z6]),(0,[z89,z1,z3,z4,z328,z6]),(0,[z162,z1,z336,z4,z5,z6]),(0,[z0,z1,z414,z157,z5,z6]),(0,[z0,z1,z3,z157,z481,z6]),(0,[z0,z199,z3,z346,z4,z6]),(0,[z0,z1143,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1197,z6])]],
   [[(0,[z1,z48,z336,z4,z5,z6]),(0,[z1,z123,z3,z77,z21,z6]),(0,[z1,z3,z4,z21,z49,z6]),(0,[z70,z1,z3,z4,z21,z6]),(0,[z0,z57,z3,z4,z359,z6]),(0,[z173,z1,z3,z4,z56,z6]),(0,[z0,z3,z4,z55,z6,z177]),(0,[z0,z1,z3,z4,z422,z6]),(0,[z1,z33,z72,z4,z34,z6]),(0,[z0,z1198,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1199,z6]),(0,[z0,z1,z3,z4,z1200,z6]),(0,[z0,z3,z346,z4,z21,z6]),(0,[z81,z1,z3,z4,z5,z439]),(1,[z0,z3,z4,z55,z439]),(0,[z0,z33,z3,z4,z596,z6]),(0,[z0,z3,z67,z501,z94,z6])],[(0,[z0,z1,z3,z149,z55,z6]),(0,[z0,z1,z3,z4,z1201,z6]),(0,[z0,z1,z3,z4,z1202,z6]),(0,[z0,z1,z3,z67,z96,z6]),(0,[z0,z1,z3,z4,z962,z6]),(0,[z30,z0,z3,z4,z55,z499]),(0,[z0,z1,z3,z4,z1203,z6])],[(0,[z0,z64,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1204,z6]),(0,[z0,z3,z1140,z4,z51,z6]),(0,[z0,z428,z3,z157,z5,z6]),(0,[z0,z1,z3,z4,z1205,z6]),(0,[z0,z1,z3,z1206,z5,z6]),(0,[z1207,z1,z3,z4,z5,z6]),(0,[z1208,z1,z3,z4,z5,z6]),(0,[z0,z3,z662,z4,z52,z6]),(0,[z91,z1,z3,z394,z5,z6])],[(0,[z0,z3,z4,z85,z6,z42]),(0,[z0,z1,z336,z4,z5,z6]),(0,[z129,z1,z3,z4,z434,z6]),(0,[z0,z1209,z3,z4,z5,z6]),(0,[z0,z57,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z1210,z6])],[(0,[z0,z1,z3,z4,z447,z6]),(0,[z63,z1,z3,z929,z5,z6]),(0,[z0,z1,z3,z4,z1211,z6]),(0,[z89,z1,z3,z4,z53,z6]),(0,[z0,z1,z3,z4,z1212,z6]),(0,[z0,z1,z3,z4,z1213,z6]),(0,[z0,z58,z23,z103,z5,z6]),(0,[z0,z3,z4,z5,z1214,z6])],[(0,[z1,z3,z752,z4,z5,z6]),(0,[z0,z40,z3,z4,z359,z6]),(0,[z0,z1,z3,z4,z1215,z6]),(0,[z0,z1,z3,z4,z52,z499]),(0,[z0,z1,z3,z1216,z4,z6]),(0,[z0,z1,z33,z4,z1039,z6])],[(0,[z460,z0,z3,z4,z5,z42]),(0,[z0,z1,z3,z4,z1217,z6]),(0,[z1,z3,z462,z4,z5,z6]),(0,[z0,z3,z771,z140,z5,z6]),(0,[z0,z1,z4,z5,z766,z36]),(0,[z1218,z1,z3,z4,z5,z6])]],
   [[(0,[z89,z1,z414,z4,z21,z6]),(0,[z0,z1,z33,z4,z348,z6]),(0,[z1219,z1,z3,z4,z5,z6]),(0,[z236,z0,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z1220,z6])],[(0,[z0,z90,z3,z4,z55,z6]),(0,[z0,z1,z3,z251,z21,z6]),(0,[z0,z1,z3,z31,z56,z6]),(0,[z848,z1,z3,z4,z5,z6])],[(0,[z1,z72,z3,z4,z21,z6]),(0,[z0,z1221,z3,z4,z5,z6]),(0,[z0,z1222,z3,z4,z5,z6]),(0,[z0,z1223,z3,z4,z5,z6]),(0,[z0,z411,z3,z4,z21,z6]),(0,[z0,z40,z3,z4,z55,z6]),(0,[z684,z0,z3,z4,z55,z6]),(0,[z0,z1,z1224,z4,z5,z6])],[(0,[z531,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z516,z4,z221]),(0,[z81,z1,z3,z4,z1152,z6]),(0,[z30,z0,z147,z4,z55,z6]),(0,[z169,z0,z3,z140,z5,z6]),(0,[z0,z1,z3,z55,z6,z310]),(0,[z0,z633,z3,z4,z55,z6]),(0,[z0,z3,z4,z55,z406,z6]),(0,[z0,z1,z3,z4,z1225,z6]),(0,[z0,z1,z45,z3,z5,z751])],[(0,[z0,z1,z1226,z4,z5,z6]),(0,[z0,z1227,z3,z4,z5,z6]),(0,[z89,z428,z3,z4,z21,z6]),(0,[z175,z1,z3,z4,z21,z6]),(0,[z1228,z1,z3,z4,z5,z6]),(0,[z1,z3,z4,z604,z52,z6]),(0,[z1229,z0,z3,z4,z5,z6])],[(0,[z0,z90,z3,z4,z19,z6]),(0,[z0,z3,z4,z1007,z21,z6]),(0,[z312,z1,z3,z4,z21,z6]),(0,[z0,z146,z336,z4,z5,z6]),(0,[z0,z1,z3,z205,z55,z6]),(0,[z0,z1,z1230,z4,z5,z6]),(0,[z0,z1,z3,z67,z88,z6]),(0,[z0,z1,z3,z4,z732,z6]),(0,[z0,z1,z3,z4,z1231,z6])],[(0,[z0,z1,z3,z4,z1232,z6]),(0,[z0,z57,z3,z4,z55,z42]),(0,[z0,z1,z3,z4,z1233,z6])],[(0,[z0,z1,z3,z4,z1234,z6]),(0,[z63,z1,z3,z77,z52,z6]),(0,[z0,z1,z3,z4,z1235,z6]),(0,[z0,z3,z253,z4,z55,z6]),(0,[z0,z1,z45,z3,z55,z14]),(0,[z82,z1,z3,z4,z356,z6]),(0,[z0,z1,z3,z4,z5,z751])]],
   [[(0,[z0,z1,z3,z4,z1236,z6]),(0,[z1092,z1,z3,z4,z55,z6])],[(0,[z0,z1,z3,z4,z1237,z6]),(0,[z17,z0,z3,z4,z992,z6]),(0,[z169,z0,z3,z4,z21,z6]),(0,[z162,z1,z3,z157,z5,z6]),(0,[z0,z1,z3,z4,z1238,z6]),(0,[z0,z1,z1239,z3,z4,z6]),(0,[z0,z987,z3,z4,z311,z6])],[(0,[z48,z3,z77,z140,z5,z6]),(0,[z0,z1,z3,z1240,z5,z6]),(0,[z1,z3,z4,z21,z619,z6]),(0,[z0,z1,z3,z4,z1241,z6]),(0,[z0,z1,z3,z4,z481,z6]),(0,[z1,z3,z4,z21,z478,z6]),(0,[z1,z3,z4,z21,z6,z13]),(0,[z0,z1,z1242,z3,z5,z6]),(0,[z0,z1,z3,z1243,z5,z6]),(0,[z169,z0,z3,z4,z1015,z6]),(0,[z0,z1,z3,z4,z1244,z6])],[(0,[z0,z1,z3,z4,z1245,z6]),(0,[z0,z1246,z3,z4,z5,z6]),(0,[z0,z1,z3,z335,z55,z6]),(0,[z0,z1,z3,z1247,z5,z6]),(0,[z0,z1,z3,z4,z1248,z6]),(0,[z1,z3,z4,z53,z49,z6]),(0,[z0,z267,z3,z4,z55,z6]),(0,[z1249,z1,z3,z4,z5,z6]),(0,[z367,z1,z3,z4,z741,z6])],[(0,[z1,z3,z4,z77,z21,z6]),(0,[z0,z141,z3,z4,z55,z6]),(0,[z84,z1,z3,z4,z52,z6]),(0,[z0,z3,z188,z501,z4,z6])],[(0,[z1250,z0,z3,z4,z5,z6]),(0,[z0,z1,z4,z901,z55,z6]),(0,[z0,z3,z4,z200,z55,z6]),(0,[z1251,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z191,z356,z6]),(0,[z84,z3,z501,z4,z5,z6])],[(0,[z1,z3,z4,z5,z6,z375]),(0,[z0,z1252,z3,z4,z5,z6]),(0,[z0,z98,z3,z4,z359,z6]),(0,[z0,z1,z336,z4,z415,z6]),(0,[z0,z1,z3,z4,z1253,z6]),(0,[z0,z3,z4,z5,z6,z1254])],[(0,[z0,z1,z3,z4,z1255,z6]),(0,[z586,z1,z3,z4,z21,z6]),(0,[z1,z3,z4,z308,z21,z49]),(0,[z65,z0,z3,z140,z51,z6]),(0,[z173,z1,z3,z4,z5,z439]),(0,[z518,z1,z3,z4,z52,z6]),(0,[z135,z1,z3,z4,z52,z6])]],
   [[(0,[z17,z0,z3,z4,z21,z6]),(0,[z1,z349,z3,z4,z21,z6]),(0,[z89,z1,z414,z4,z5,z101]),(0,[z89,z1,z3,z4,z481,z101]),(0,[z1256,z1,z3,z4,z5,z6]),(0,[z1104,z1,z3,z4,z5,z6]),(0,[z82,z1,z3,z394,z5,z6])],[(0,[z584,z48,z3,z4,z5,z6]),(0,[z1,z48,z3,z4,z53,z6]),(0,[z15,z1,z16,z4,z447,z6]),(0,[z1,z352,z3,z4,z21,z6]),(0,[z65,z0,z3,z205,z5,z6]),(0,[z0,z3,z4,z455,z55,z6]),(0,[z0,z241,z3,z4,z55,z6]),(0,[z0,z457,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z1257,z6]),(0,[z97,z0,z3,z4,z5,z959]),(0,[z0,z1,z125,z3,z5,z6]),(0,[z0,z1,z4,z5,z6,z766]),(0,[z0,z3,z5,z6,z310,z177])],[(0,[z0,z1,z1258,z3,z4,z6]),(0,[z0,z1,z3,z4,z1259,z6]),(0,[z0,z1,z3,z157,z52,z6]),(0,[z1,z3,z4,z5,z6,z719]),(0,[z0,z98,z3,z4,z55,z6]),(0,[z198,z1,z3,z4,z366,z6]),(0,[z0,z1,z3,z4,z1260,z6]),(0,[z0,z1,z3,z1261,z5,z6]),(0,[z583,z0,z1,z4,z5,z36]),(0,[z0,z1,z3,z4,z1262,z6]),(0,[z1263,z1,z3,z4,z422,z6])],[(0,[z367,z1,z3,z4,z5,z6]),(0,[z0,z3,z130,z140,z55,z6]),(0,[z317,z1,z3,z4,z5,z6]),(0,[z0,z146,z414,z4,z5,z6]),(0,[z0,z146,z3,z4,z481,z6]),(0,[z0,z1,z414,z251,z5,z6]),(0,[z0,z1,z3,z4,z1264,z6]),(0,[z0,z648,z3,z4,z55,z6]),(0,[z0,z1,z3,z1265,z4,z6]),(0,[z367,z1,z3,z4,z372,z6]),(0,[z0,z1,z45,z3,z423,z14])],[(0,[z17,z0,z3,z4,z257,z6]),(0,[z0,z1,z3,z4,z984,z6]),(0,[z0,z1,z484,z4,z348,z6]),(0,[z89,z428,z3,z4,z5,z101])],[(0,[z0,z1,z3,z4,z1266,z6]),(0,[z0,z1,z3,z4,z53,z6]),(0,[z0,z64,z3,z4,z51,z6]),(0,[z0,z1,z3,z1267,z5,z6]),(0,[z0,z3,z140,z103,z55,z6]),(0,[z0,z1,z3,z4,z1039,z6]),(0,[z0,z3,z1268,z4,z5,z6])],[(0,[z0,z1,z3,z4,z164,z6]),(0,[z0,z1,z3,z4,z763,z6]),(0,[z173,z1,z3,z4,z52,z6]),(0,[z97,z0,z3,z4,z55,z42]),(0,[z367,z1,z3,z298,z4,z6]),(0,[z0,z1,z3,z4,z1269,z6])],[(0,[z0,z1,z3,z1270,z5,z6]),(0,[z0,z1,z3,z4,z1271,z6]),(0,[z1,z16,z4,z258,z21,z6]),(0,[z18,z1,z3,z4,z328,z6]),(0,[z0,z211,z3,z4,z164,z6]),(0,[z236,z0,z3,z4,z21,z6]),(0,[z780,z0,z3,z4,z5,z6]),(0,[z0,z428,z3,z251,z5,z6]),(0,[z0,z1,z3,z4,z116,z6]),(0,[z0,z1,z3,z4,z5,z1272]),(0,[z1273,z1,z3,z4,z5,z6])]],
   [[(0,[z1274,z0,z3,z4,z5,z6]),(1,[z1,z3,z157,z21,z6]),(0,[z0,z1,z414,z4,z21,z6]),(0,[z81,z1,z3,z4,z5,z499]),(0,[z0,z1,z3,z31,z5,z439]),(0,[z0,z1,z710,z4,z5,z6]),(0,[z0,z458,z3,z4,z5,z6]),(0,[z0,z1,z3,z394,z200,z6]),(0,[z1,z3,z4,z1275,z5,z6])],[(0,[z0,z1,z3,z4,z1276,z6]),(0,[z129,z1,z3,z4,z85,z6]),(0,[z0,z1,z3,z4,z1277,z6]),(0,[z1,z3,z462,z4,z51,z6]),(0,[z0,z3,z4,z596,z5,z6]),(0,[z518,z3,z4,z140,z5,z6]),(0,[z0,z1,z3,z4,z724,z6]),(0,[z0,z3,z1278,z4,z5,z6]),(0,[z0,z3,z1098,z4,z6,z177])],[(0,[z30,z518,z3,z4,z5,z6]),(0,[z1279,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1280,z6]),(0,[z1,z3,z4,z172,z21,z6]),(0,[z1,z3,z4,z21,z6,z651]),(0,[z0,z1,z3,z4,z1281,z6]),(0,[z0,z1282,z3,z4,z5,z6])],[(0,[z1,z3,z4,z293,z85,z6]),(0,[z17,z0,z3,z4,z51,z6]),(0,[z0,z428,z3,z4,z21,z6]),(0,[z0,z1,z3,z205,z21,z6]),(0,[z91,z57,z3,z4,z55,z6]),(0,[z0,z33,z3,z501,z4,z6]),(0,[z0,z1,z3,z1283,z5,z6])],[(0,[z0,z1,z3,z4,z464,z6]),(0,[z153,z95,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z1284,z6]),(0,[z0,z1,z3,z4,z1285,z6]),(0,[z30,z0,z3,z4,z359,z6]),(0,[z0,z3,z4,z55,z6,z295]),(0,[z97,z0,z3,z4,z168,z42]),(0,[z0,z1,z3,z1286,z4,z6]),(0,[z0,z1287,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1288,z6]),(0,[z1289,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1290,z6]),(0,[z243,z0,z1,z4,z5,z36]),(0,[z243,z0,z1,z4,z372,z36]),(0,[z1291,z1,z3,z4,z5,z6])],[(0,[z0,z90,z3,z4,z1217,z6]),(0,[z1,z3,z4,z341,z21,z6]),(0,[z0,z1,z58,z103,z21,z6]),(0,[z0,z1,z3,z4,z1292,z6]),(0,[z169,z0,z3,z205,z5,z6]),(0,[z0,z1,z3,z31,z52,z6]),(0,[z0,z3,z60,z140,z55,z6]),(0,[z0,z1,z3,z1293,z4,z6]),(0,[z0,z1,z3,z1294,z5,z6]),(0,[z0,z1,z3,z4,z1295,z6])]],
   [[(0,[z129,z1,z3,z4,z53,z6]),(0,[z0,z1,z3,z5,z6,z1177]),(0,[z0,z3,z4,z945,z55,z6]),(0,[z91,z1,z3,z4,z1220,z6]),(0,[z0,z1,z3,z1296,z5,z6]),(0,[z1297,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1298,z6])],[(0,[z0,z1,z3,z4,z249,z6]),(0,[z1,z3,z4,z85,z49,z6]),(0,[z672,z0,z3,z4,z55,z6]),(0,[z0,z1,z3,z1299,z4,z6]),(0,[z0,z3,z121,z4,z55,z6]),(0,[z1,z3,z4,z5,z6,z1300]),(0,[z1,z736,z3,z4,z5,z6]),(0,[z0,z3,z4,z52,z6,z177]),(0,[z0,z1,z3,z4,z372,z6]),(0,[z243,z0,z1,z298,z4,z36]),(0,[z1,z3,z4,z5,z6,z1301]),(0,[z1,z3,z4,z423,z6,z13])],[(0,[z0,z211,z3,z4,z5,z6]),(0,[z0,z1,z3,z335,z21,z6]),(0,[z0,z1,z3,z4,z1302,z6]),(0,[z0,z1,z3,z4,z1303,z6]),(0,[z0,z41,z3,z191,z5,z6]),(0,[z169,z0,z58,z103,z5,z6]),(0,[z0,z1,z3,z4,z1304,z6]),(0,[z0,z411,z3,z67,z94,z6]),(0,[z0,z1,z3,z4,z1305,z6])],[(0,[z236,z0,z3,z5,z6,z310])],[(0,[z0,z1,z3,z4,z1306,z6]),(0,[z89,z1,z3,z4,z5,z62]),(0,[z0,z1,z414,z4,z51,z6]),(0,[z0,z411,z3,z4,z183,z6]),(0,[z0,z41,z3,z4,z200,z6])],[(0,[z0,z1,z3,z4,z52,z6]),(0,[z0,z48,z3,z76,z5,z6]),(0,[z198,z1,z3,z4,z1162,z6]),(0,[z0,z1,z3,z4,z1307,z6]),(0,[z0,z3,z346,z4,z55,z6]),(0,[z0,z41,z3,z4,z945,z6]),(0,[z1,z199,z72,z3,z4,z6])],[(0,[z0,z1,z3,z1308,z5,z6]),(0,[z0,z1,z3,z4,z1309,z6]),(0,[z1,z3,z4,z763,z21,z6]),(0,[z102,z0,z3,z4,z359,z6]),(0,[z0,z3,z501,z4,z5,z6]),(0,[z1,z3,z978,z4,z55,z6])],[(0,[z26,z48,z3,z4,z5,z6]),(0,[z0,z1,z1310,z4,z5,z6]),(0,[z228,z0,z3,z140,z5,z6]),(0,[z0,z211,z3,z77,z5,z6]),(0,[z0,z1,z3,z4,z1311,z6]),(0,[z0,z3,z4,z985,z55,z6]),(0,[z0,z3,z350,z4,z55,z6])]],
   [[(0,[z91,z48,z3,z4,z5,z6]),(0,[z1312,z0,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z178,z6]),(0,[z1,z3,z196,z77,z21,z6]),(0,[z222,z1,z3,z4,z21,z6]),(0,[z360,z1,z3,z4,z21,z6]),(0,[z0,z428,z3,z4,z51,z6]),(0,[z65,z518,z3,z140,z5,z6]),(0,[z0,z3,z4,z55,z42,z36]),(0,[z1,z3,z4,z1168,z5,z6]),(0,[z0,z1,z3,z4,z1313,z6]),(0,[z0,z1,z3,z4,z1314,z6])],[(0,[z0,z57,z3,z4,z85,z6]),(0,[z95,z0,z3,z4,z359,z6]),(0,[z639,z1,z3,z4,z21,z6]),(0,[z1,z3,z20,z77,z21,z6]),(0,[z0,z1,z3,z4,z1315,z6]),(0,[z0,z1,z3,z4,z1316,z6]),(0,[z30,z0,z147,z4,z56,z6])],[(0,[z0,z1,z385,z3,z5,z14]),(0,[z1,z3,z4,z21,z690,z6]),(0,[z29,z0,z3,z4,z55,z6]),(0,[z40,z518,z3,z4,z5,z6]),(0,[z102,z0,z3,z4,z55,z6]),(0,[z1,z3,z4,z1317,z5,z6]),(0,[z1318,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z6,z953])],[(0,[z26,z48,z3,z4,z52,z6]),(0,[z0,z1,z3,z4,z1319,z6]),(0,[z0,z1,z1320,z3,z4,z6]),(0,[z0,z1,z125,z3,z51,z6]),(0,[z89,z1,z3,z4,z52,z101]),(0,[z0,z1,z3,z205,z56,z6]),(0,[z1321,z1,z3,z4,z5,z6]),(0,[z362,z0,z3,z4,z55,z6]),(0,[z383,z1,z3,z4,z52,z6]),(0,[z0,z3,z4,z5,z1322,z6]),(0,[z0,z1323,z3,z4,z5,z6])],[(0,[z17,z0,z3,z335,z5,z6]),(0,[z0,z1,z3,z4,z1324,z6]),(0,[z0,z1,z3,z4,z21,z439]),(0,[z0,z1,z3,z394,z21,z6]),(0,[z0,z1,z336,z157,z5,z6]),(0,[z0,z1,z3,z5,z6,z1325]),(0,[z0,z1,z3,z4,z1326,z6]),(0,[z0,z1,z3,z4,z1327,z6]),(0,[z0,z1,z33,z506,z4,z6]),(0,[z0,z1,z3,z4,z1328,z6]),(0,[z0,z1,z3,z4,z1329,z6])],[(0,[z0,z3,z4,z292,z6,z42]),(0,[z0,z1,z3,z4,z5,z1330]),(0,[z129,z211,z3,z4,z5,z6]),(0,[z1,z3,z409,z77,z21,z6]),(0,[z0,z1331,z3,z4,z5,z6]),(0,[z367,z1,z3,z4,z51,z6]),(0,[z317,z1,z3,z4,z51,z6]),(0,[z0,z1,z3,z4,z214,z6]),(0,[z0,z11,z3,z346,z4,z6])],[(0,[z95,z0,z3,z191,z5,z6]),(0,[z0,z1332,z3,z4,z5,z6]),(0,[z160,z1,z3,z4,z21,z6]),(0,[z1,z3,z4,z21,z555,z6]),(0,[z0,z1,z3,z4,z1333,z6]),(0,[z0,z146,z3,z4,z52,z6]),(0,[z173,z1,z3,z4,z5,z499]),(0,[z0,z411,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z1334,z6])],[(0,[z0,z1,z3,z1335,z5,z6]),(0,[z0,z40,z3,z4,z85,z6]),(0,[z0,z1,z3,z1336,z5,z6]),(0,[z0,z1337,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1338,z6]),(0,[z1,z3,z4,z929,z5,z6]),(0,[z0,z1,z3,z4,z365,z6]),(0,[z0,z1,z3,z4,z1339,z6]),(0,[z1340,z1,z3,z4,z5,z6])]],
   [[(0,[z228,z1,z3,z77,z5,z6]),(0,[z0,z1,z3,z4,z1341,z6]),(0,[z1,z3,z4,z434,z49,z6]),(0,[z0,z1,z3,z4,z1342,z6]),(0,[z0,z1,z3,z4,z1343,z6]),(0,[z0,z1,z3,z4,z1344,z6]),(0,[z0,z1,z3,z4,z381,z6])],[(0,[z1,z48,z3,z172,z5,z6]),(0,[z89,z1,z3,z4,z1345,z6]),(0,[z1,z3,z4,z21,z6,z701]),(0,[z0,z1,z921,z3,z4,z6])],[(0,[z625,z0,z3,z140,z5,z6]),(0,[z1,z35,z16,z4,z21,z6]),(0,[z0,z1141,z3,z4,z21,z6]),(0,[z313,z1,z3,z4,z21,z6]),(0,[z113,z0,z3,z4,z359,z6]),(0,[z0,z458,z3,z4,z51,z6]),(0,[z1346,z1,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z415,z6]),(0,[z0,z3,z4,z596,z51,z6]),(0,[z0,z1347,z3,z4,z5,z6]),(0,[z0,z1,z4,z1039,z34,z6]),(0,[z0,z3,z4,z1348,z5,z6])],[(0,[z153,z95,z3,z4,z21,z6]),(0,[z129,z1,z3,z130,z21,z6]),(0,[z459,z0,z3,z4,z55,z6]),(0,[z1,z11,z3,z462,z4,z6]),(0,[z236,z0,z3,z4,z1109,z6]),(0,[z1,z3,z1349,z4,z5,z6]),(0,[z1350,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1351,z6])],[(0,[z1,z3,z16,z4,z85,z6]),(0,[z15,z1,z16,z4,z5,z6]),(0,[z0,z1,z3,z172,z5,z6]),(0,[z0,z3,z4,z5,z6,z1352]),(0,[z0,z64,z3,z4,z55,z6]),(0,[z89,z1,z336,z4,z21,z6]),(0,[z1,z3,z261,z4,z21,z6]),(0,[z81,z1,z3,z4,z116,z6]),(0,[z0,z1,z3,z1353,z5,z6]),(0,[z0,z3,z4,z55,z6,z511]),(0,[z0,z57,z3,z4,z293,z6]),(0,[z169,z0,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z772,z6]),(0,[z1354,z1,z3,z4,z5,z6])],[(0,[z89,z1,z3,z4,z144,z6]),(0,[z0,z1,z3,z4,z1355,z6]),(0,[z0,z1,z3,z4,z1356,z6]),(0,[z0,z1,z3,z1357,z5,z6]),(0,[z0,z1,z3,z4,z1358,z6])],[(0,[z0,z1359,z3,z4,z5,z6]),(0,[z1,z3,z4,z157,z21,z6]),(0,[z1,z441,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z1360,z6]),(0,[z0,z3,z4,z51,z6,z177]),(0,[z0,z912,z3,z4,z5,z6]),(0,[z0,z1,z3,z31,z5,z499]),(0,[z0,z57,z3,z191,z55,z6]),(0,[z0,z1,z3,z4,z1361,z6]),(0,[z1362,z1,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1363,z6]),(0,[z1364,z0,z3,z4,z5,z6])]],
   [[(0,[z17,z48,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1365,z6]),(0,[z0,z1,z3,z4,z51,z439]),(0,[z0,z1,z3,z394,z51,z6]),(0,[z243,z0,z1,z4,z51,z36]),(0,[z0,z1,z3,z1042,z4,z6]),(0,[z0,z1,z3,z4,z1366,z6])],[(0,[z0,z48,z3,z4,z328,z6]),(0,[z0,z1,z3,z4,z1367,z6]),(0,[z15,z1,z16,z4,z52,z6]),(0,[z0,z1368,z3,z4,z5,z6]),(0,[z0,z3,z4,z55,z6,z439]),(0,[z0,z40,z3,z4,z366,z6]),(0,[z1031,z1,z3,z4,z55,z6]),(0,[z1,z3,z462,z4,z55,z6]),(0,[z0,z3,z4,z23,z52,z6]),(0,[z1,z3,z4,z372,z6,z375])],[(0,[z1,z48,z3,z76,z5,z6]),(0,[z668,z1,z3,z4,z21,z6])],[(0,[z0,z1,z3,z4,z1369,z6]),(0,[z63,z1,z3,z77,z164,z6]),(0,[z1,z3,z4,z5,z6,z13]),(0,[z0,z1,z58,z285,z5,z6]),(0,[z0,z3,z176,z140,z55,z6]),(0,[z0,z1,z529,z103,z5,z6]),(0,[z0,z40,z3,z4,z293,z6]),(0,[z1263,z1,z3,z4,z5,z6])],[(0,[z173,z48,z3,z4,z5,z6]),(0,[z17,z0,z3,z4,z55,z6]),(0,[z1,z211,z3,z77,z5,z6]),(0,[z0,z146,z3,z4,z415,z6])],[(0,[z0,z1,z3,z4,z1370,z6]),(0,[z1,z3,z4,z51,z53,z6]),(0,[z0,z1,z3,z4,z5,z499]),(0,[z236,z0,z3,z4,z5,z439]),(0,[z0,z3,z4,z55,z6,z527])],[(0,[z0,z1,z3,z76,z5,z6]),(0,[z0,z1,z3,z149,z52,z6]),(0,[z446,z1,z3,z4,z21,z6]),(0,[z0,z1,z3,z4,z263,z6]),(0,[z0,z3,z4,z397,z55,z6]),(0,[z360,z1,z3,z4,z85,z6]),(0,[z236,z0,z3,z4,z5,z122])],[(0,[z0,z98,z3,z4,z85,z6]),(0,[z0,z1,z1371,z4,z5,z6]),(0,[z0,z1,z3,z4,z1372,z6]),(0,[z0,z458,z3,z202,z4,z221])]],
   [[(0,[z30,z0,z3,z4,z292,z6]),(0,[z17,z0,z3,z4,z19,z6]),(0,[z0,z1,z3,z392,z4,z143]),(0,[z0,z3,z501,z4,z51,z6]),(0,[z30,z0,z147,z4,z5,z439]),(0,[z0,z1,z3,z844,z5,z6])],[(0,[z0,z1,z3,z4,z1373,z6]),(0,[z153,z1,z3,z172,z5,z6]),(0,[z0,z1,z3,z4,z1374,z6]),(0,[z0,z1,z3,z4,z1375,z6]),(0,[z0,z1,z3,z4,z1376,z6]),(0,[z0,z1,z1377,z3,z5,z6]),(0,[z30,z0,z120,z4,z5,z6]),(0,[z0,z556,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z1378,z6])],[(0,[z0,z1,z3,z76,z52,z6]),(0,[z0,z1,z3,z4,z1379,z6]),(0,[z0,z1,z752,z4,z5,z6]),(0,[z222,z1,z3,z4,z829,z6]),(0,[z0,z1,z3,z516,z4,z468]),(0,[z0,z1,z3,z51,z6,z310]),(0,[z0,z1,z3,z4,z831,z6]),(0,[z0,z1,z3,z205,z5,z439]),(0,[z0,z1,z3,z332,z4,z333]),(0,[z1,z1380,z3,z4,z5,z6])],[(0,[z0,z48,z3,z191,z5,z6]),(0,[z0,z1,z3,z4,z1381,z6]),(0,[z0,z1,z3,z4,z1382,z6]),(0,[z367,z1,z74,z4,z5,z6]),(0,[z1,z3,z4,z604,z5,z6]),(0,[z81,z1,z3,z4,z52,z6]),(0,[z518,z1,z3,z4,z731,z6]),(0,[z65,z0,z3,z140,z259,z6]),(1,[z0,z3,z4,z945,z6]),(0,[z1,z3,z540,z462,z4,z6]),(0,[z1,z3,z202,z462,z4,z6]),(0,[z1383,z1,z3,z4,z5,z6])],[(0,[z26,z48,z3,z76,z5,z6]),(0,[z1,z3,z4,z469,z21,z6]),(0,[z0,z1,z414,z4,z55,z6]),(0,[z0,z1,z3,z4,z1384,z6])],[(0,[z340,z48,z3,z4,z5,z6]),(0,[z0,z3,z4,z140,z292,z6]),(0,[z0,z90,z3,z4,z52,z6]),(0,[z0,z64,z3,z4,z434,z6]),(0,[z89,z1,z336,z4,z5,z101]),(0,[z91,z1,z3,z4,z52,z6]),(0,[z1,z3,z462,z4,z94,z6])],[(0,[z0,z1385,z3,z4,z5,z6]),(0,[z63,z1,z3,z77,z5,z6]),(0,[z454,z1,z3,z4,z21,z6]),(0,[z65,z0,z3,z140,z21,z6]),(0,[z0,z233,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z1386,z6])],[(0,[z0,z1,z3,z172,z257,z6]),(0,[z63,z211,z3,z77,z5,z6]),(0,[z0,z1,z3,z4,z1387,z6]),(0,[z89,z1,z3,z157,z21,z6]),(0,[z1,z3,z4,z1345,z21,z6]),(0,[z0,z115,z3,z4,z249,z6]),(0,[z30,z0,z147,z4,z52,z6]),(0,[z236,z0,z3,z4,z1154,z6]),(0,[z0,z1,z3,z1388,z5,z6])]],
   [[(0,[z89,z1,z3,z4,z192,z6]),(0,[z1,z187,z16,z4,z21,z6]),(0,[z17,z0,z3,z4,z1172,z6]),(0,[z1,z3,z4,z77,z434,z6]),(0,[z1,z3,z475,z4,z21,z6]),(0,[z89,z1,z3,z4,z5,z201]),(0,[z0,z428,z3,z4,z55,z6]),(0,[z0,z1,z336,z251,z5,z6]),(0,[z0,z3,z4,z1017,z55,z6]),(0,[z0,z1,z3,z4,z985,z6]),(0,[z0,z1,z3,z4,z1389,z6]),(0,[z0,z380,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z782,z6]),(0,[z0,z1,z3,z4,z1390,z6]),(0,[z0,z3,z1391,z4,z5,z6]),(0,[z1392,z1,z3,z4,z5,z6])],[(0,[z340,z0,z3,z4,z55,z6]),(0,[z0,z1,z3,z4,z1345,z6]),(0,[z97,z0,z3,z4,z5,z439]),(0,[z0,z98,z3,z4,z366,z6]),(0,[z0,z1,z3,z394,z356,z6]),(0,[z0,z1393,z3,z4,z5,z6])],[(0,[z0,z1,z3,z4,z1394,z6]),(0,[z28,z1,z3,z4,z21,z6]),(0,[z1,z3,z929,z77,z5,z6]),(0,[z1,z3,z4,z328,z49,z6]),(0,[z0,z146,z3,z4,z1375,z6])],[(0,[z26,z48,z3,z4,z100,z6]),(0,[z153,z1,z336,z4,z5,z6]),(0,[z18,z1,z3,z172,z21,z6]),(0,[z84,z1,z3,z4,z5,z6]),(0,[z0,z115,z3,z4,z52,z6]),(0,[z173,z1,z3,z4,z116,z6]),(0,[z0,z1,z3,z4,z5,z1395]),(0,[z0,z98,z3,z4,z293,z6]),(0,[z0,z1,z58,z103,z55,z6]),(0,[z0,z1,z125,z3,z55,z6]),(0,[z0,z1,z45,z3,z52,z14]),(0,[z1,z1396,z3,z4,z5,z6])],[(0,[z428,z48,z3,z4,z5,z6]),(0,[z0,z1,z3,z1397,z5,z6]),(0,[z0,z1,z3,z4,z1398,z6]),(0,[z0,z64,z3,z4,z21,z6]),(0,[z0,z1,z3,z917,z4,z5]),(0,[z1,z3,z336,z4,z21,z6]),(0,[z0,z578,z3,z4,z55,z6]),(0,[z1399,z1,z3,z4,z5,z6])],[(0,[z770,z48,z3,z4,z5,z6]),(0,[z1,z48,z3,z157,z5,z6]),(0,[z0,z1,z3,z4,z1400,z6]),(0,[z0,z1,z3,z1401,z5,z6]),(0,[z0,z1402,z3,z4,z5,z6]),(0,[z0,z1403,z3,z4,z5,z6]),(0,[z0,z1,z3,z4,z1404,z6]),(0,[z0,z1,z336,z4,z21,z6]),(0,[z0,z1209,z3,z4,z21,z6]),(0,[z0,z1,z3,z1405,z5,z6]),(0,[z0,z3,z4,z276,z55,z6]),(0,[z367,z1,z3,z4,z55,z6]),(0,[z317,z1,z3,z4,z55,z6]),(0,[z0,z1,z45,z3,z5,z629])],[(0,[z518,z1,z3,z4,z5,z6]),(0,[z135,z1,z3,z4,z5,z6]),(0,[z0,z41,z3,z205,z5,z6]),(0,[z207,z0,z3,z4,z55,z6])],[(0,[z0,z90,z3,z4,z1338,z6]),(0,[z0,z1,z3,z172,z51,z6]),(0,[z1,z3,z480,z77,z21,z6]),(0,[z1406,z0,z3,z4,z5,z6]),(0,[z0,z1,z885,z4,z5,z6]),(0,[z0,z1407,z3,z4,z5,z6])]]]

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 460).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 920).take 460) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb3 : chunkB SB 1 ((bkA.flatten.flatten.drop 1380).take 64) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1444)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [460, 460, 460, 64] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_cons pb3 (windowsG_nil pbend))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 68).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 68).take 68).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 136).take 71).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 207).take 49).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [68, 68, 71, 49] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

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

end PEqualNP.Outside.L_meta_36767

theorem PEqualNP.Outside.L_meta_36767 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4008373480 * 2 ^ 32 + 4008373376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4008373480 * 2 ^ 32 + 4008373376) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_36767.solve