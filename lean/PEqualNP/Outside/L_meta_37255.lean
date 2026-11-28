import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_37255

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
  Nat.testBit (4277071594 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x20021210a30e3189#64 ++ 0x240042421461c631#64 ++ 0xd8163633e31e739d#64 ++ 0xfb02c6c67c63ce73#64 : BitVec 256),
   (0x4002c2c5836294a1#64 ++ 0x88005858b06c5294#64 ++ 0xbe2bcbcd83e39ce3#64 ++ 0xf7c57979b07c739c#64 : BitVec 256),
   (0x80cc0c0a0c014a52#64 ++ 0x501981814180294a#64 ++ 0x71cc0c0e1c03ffff#64 ++ 0xee398181c3807fff#64 : BitVec 256),
   (0x03700f7015b41f04#64 ++ 0x606e01ee02b683e0#64 ++ 0xfbf00ff01ffc1f07#64 ++ 0x5f7e01fe03ff83e0#64 : BitVec 256),
   (0x05bf70001adbe007#64 ++ 0x80b7ee00035b7c00#64 ++ 0xfdfff0001fffe007#64 ++ 0x3fbffe0003fffc00#64 : BitVec 256),
   (0x01fdadaf40000000#64 ++ 0x003fb5b5e8000000#64 ++ 0xf7ffffffe0000000#64 ++ 0xfefffffffc000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.or, [2, 5]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [6, 12]⟩, ⟨.or, [13, 7]⟩, ⟨.and, [14, 11]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0x27e9c9cc00000000 0x04fd393980000000

def z1 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7ffffffe0000000 0xfefffffffc000000

def z2 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf00ff01ffc1f07 0x5f7e01fe03ff83e0

def z3 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff0001fffe007 0x3fbffe0003fffc00

def z4 : W := mkw 0x21ffbfbfe30e3189 0x243ff7f7fc61c631 0xffffffffe31e739d 0xfffffffffc63ce73

def z5 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xbe2bcbcd83e39ce3 0xf7c57979b07c739c

def z6 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x71cc0c0e1c03ffff 0xee398181c3807fff

def z7 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xd8163633e31e739d 0xfb02c6c67c63ce73

def z8 : W := mkw 0x408fe08fc24280a1 0x8811fc11f8485014 0x040ff00fe00380e0 0xa081fe01fc00701c

def z9 : W := mkw 0x0533700012daa005 0x80a66e00025b5400 0x8c33f00003fc0000 0x11867e00007f8000

def z10 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7fffffffc03ffff 0xfeffffffff807fff

def z11 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xfe3fffffe3ffffff 0xffc7fffffc7fffff

def z12 : W := mkw 0x0000021001041100 0x2000004200208220 0xd8100630031c1305 0x5b0200c600638260

def z13 : W := mkw 0x4002c2d5836695a1 0xa800585ab06cd2b4 0xfe3bcffd83ff9fe7 0xffc779ffb07ff3fc

def z14 : W := mkw 0x4002c285834290a1 0x88005850b0685214 0x9c0bc20d830390e1 0xf3817841b060721c

def z15 : W := mkw 0x01700c0014900a04 0x402e018002920140 0xf9f00c001ffc1f07 0x5f3e018003ff83e0

def z16 : W := mkw 0xa0ce1e1aaf0f7bdb 0x7419c3c355e1ef7b 0xf9de3e3fff1fffff 0xff3bc7c7ffe3ffff

def z17 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0x2629c9cc00e18c62 0x04c53939801c318c

def z18 : W := mkw 0x45bff0c51afbe427 0x88b7fe18a35f7c84 0xfffff9cc1fffec67 0x3fffff3983fffd8c

def z19 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xd8100630031e739d 0x5b0200c60063ce73

def z20 : W := mkw 0x83700f701db55f56 0x706e01ee03b6abea 0xfbf00ff01fffffff 0x5f7e01fe03ffffff

def z21 : W := mkw 0x4372cff597f69fa5 0xe86e59feb2fed3f4 0xfffbcffd9fff9fe7 0xffff79ffb3fff3fc

def z22 : W := mkw 0x83fc0f7a1db55f56 0x707f81ef43b6abea 0xfbfc0ffe1fffffff 0xff7f81ffc3ffffff

def z23 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xcbf007f01ffc0304 0x197e00fe03ff8060

def z24 : W := mkw 0x0131212040000000 0x0026242408000000 0x0010303060000000 0x000206060c000000

def z25 : W := mkw 0x0000000000000000 0x0000000000000000 0x500404020002739d 0xea00808040004e73

def z26 : W := mkw 0x048f70000a4be003 0x8091ee0001497c00 0xbc2ff00003e3e003 0x3785fe00007c7c00

def z27 : W := mkw 0x00400c0004000a00 0x4008018000800140 0x71c00c001c001f07 0x4e380180038003e0

def z28 : W := mkw 0x01bda1af40000000 0x0037b435e8000000 0x863ff3ffe0000000 0xb0c7fe7ffc000000

def z29 : W := mkw 0x008c000008014002 0x0011800001002800 0x71cc00001c03e007 0x2e39800003807c00

def z30 : W := mkw 0x85ff7c0a1edbea57 0xd0bfef8143db7d4a 0xfdfffc0e1fffffff 0xffbfff81c3ffffff

def z31 : W := mkw 0x0002020083021081 0x0000404010604210 0x9802020183021081 0xf300404030604210

def z32 : W := mkw 0x0200025015b41f04 0x6040004a02b683e0 0x080000001ffc1f07 0x0100000003ff83e0

def z33 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x41c404021c00631c 0x0838808043800c63

def z34 : W := mkw 0x0330037011b41504 0x2066006e023682a0 0x8a3003f003fc0000 0x1146007e007f8000

def z35 : W := mkw 0x03700d3014940b04 0x606e01a602928160 0x41d004301c1c0304 0x083a008603838060

def z36 : W := mkw 0x25bf7210bbdff18f 0xa4b7ee42177bfe31 0xfdfff633fffff39f 0xffbffec67ffffe73

def z37 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0x8633f3f1e0000000 0x10c67e7e3c000000

def z38 : W := mkw 0x03700d6014b00e04 0x406e01ac029601c0 0x23e009c01ce00c02 0x047c0138039c0180

def z39 : W := mkw 0x01fd2d2a40000000 0x003fa5a548000000 0xf3f43ff260000000 0x5e7e87fe4c000000

def z40 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x21c8080c1c018c62 0x043901018380318c

def z41 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0x77edcdce1c03ffff 0xeefdb9b9c3807fff

def z42 : W := mkw 0x0000000000000000 0x0000000000000000 0x71c000001c000007 0x0e38000003800000

def z43 : W := mkw 0x01fdafef41201400 0x003fb5fde8240280 0xffffffffe3e01c03 0xfffffffffc7c0380

def z44 : W := mkw 0x05ff7c001edbea07 0xc0bfef8003db7d40 0xfdfffc001fffff07 0x7fbfff8003ffffe0

def z45 : W := mkw 0x25ffffbffbdff18f 0xa4bffff7ff7bfe31 0xfffffffffffff39f 0xfffffffffffffe73

def z46 : W := mkw 0x808c00000c014a52 0x501180000180294a 0x71cc00001c03ffff 0x2e39800003807fff

def z47 : W := mkw 0x040250001adbe007 0x80804a00035b7c00 0x080000001fffe007 0x0100000003fffc00

def z48 : W := mkw 0x01bda08f40000000 0x0037b411e8000000 0xf5fff00fe0000000 0xbebffe01fc000000

def z49 : W := mkw 0x0200037001241500 0x2040006e002482a0 0x020003f000000000 0x0040007e00000000

def z50 : W := mkw 0x20021000a20a2089 0x0400420014414411 0xd0163633e0026098 0xfa02c6c67c004c13

def z51 : W := mkw 0x048e50001adbe007 0x8091ca00035b7c00 0x79cc00001fffe007 0x2f39800003fffc00

def z52 : W := mkw 0x03fdadef54b00e04 0x407fb5bdea9601c0 0xf7fffffffce00c02 0xfeffffffff9c0180

def z53 : W := mkw 0x20021250a32e3589 0x2400424a1465c6b1 0xfa363ff3e3fe7f9f 0xff46c7fe7c7fcff3

def z54 : W := mkw 0x05bd300018996006 0x00b7a60003132c00 0x41d430001c1c6004 0x083a860003838c00

def z55 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0x8e23cbcd83e01ce0 0xd1c47979b07c039c

def z56 : W := mkw 0x60025250a36eb5a9 0xac004a4a146dd6b5 0x0800000003ffffff 0x01000000007fffff

def z57 : W := mkw 0xa0cc1c1a2c0d6b5a 0x741983834581ad6b 0x71dc3c3e7c1fffff 0xee3b8787cf83ffff

def z58 : W := mkw 0x01bd200000000000 0x0037a40000000000 0xf5fff00000000000 0x3ebffe0000000000

def z59 : W := mkw 0x07fd6d601cf1ce06 0xc0ffadac039e39c0 0x27e9c9c01ce18c02 0x04fd3938039c3180

def z60 : W := mkw 0x20001010200c2108 0x2400020204018421 0x40143432601c631c 0x080286864c038c63

def z61 : W := mkw 0x23721f70b7be3f8d 0x646e43ee16f7c7f1 0xfbf63ff3fffe7f9f 0xff7ec7fe7fffcff3

def z62 : W := mkw 0x0000024001201400 0x0000004800240280 0xba200bc003e01c03 0x57440178007c0380

def z63 : W := mkw 0x00021000020a2001 0x0000420000414400 0xd8163402031e739d 0xfb02c6804063ce73

def z64 : W := mkw 0x0002828583021081 0x00005050b0604210 0xbe2bcbcd83021081 0xf7c57979b0604210

def z65 : W := mkw 0x808c000a08014052 0x101180014100280a 0x000c000e0003e0f8 0xa0018001c0007c1f

def z66 : W := mkw 0x20021000a20a2089 0x0400420014414411 0x00023001e0000000 0x000046003c000000

def z67 : W := mkw 0x20021000a20a2089 0x0400420014414411 0x00063003e0026098 0xa000c6007c004c13

def z68 : W := mkw 0x0000808500000000 0x00001010a0000000 0xf63fffffe0000000 0xfec7fffffc000000

def z69 : W := mkw 0xc0cececf8f63def3 0xd819d9d9f1ec7bde 0xffefcfcf9fe3ffff 0xfffdf9f9f3fc7fff

def z70 : W := mkw 0x008c000000000000 0x0011800000000000 0x71cc000000000000 0x2e39800000000000

def z71 : W := mkw 0x00408daf40000000 0x000811b5e8000000 0x02000fffe0000000 0xc04001fffc000000

def z72 : W := mkw 0x0130000010900004 0x0026000002120000 0xf9f000001ffc0007 0x1f3e000003ff8000

def z73 : W := mkw 0x20021000a20a2089 0x0400420014414411 0xd8163003e31e609d 0xbb02c6007c63cc13

def z74 : W := mkw 0x00021000020a2001 0x0000420000414400 0xd8163000031e6005 0x3b02c6000063cc00

def z75 : W := mkw 0xa5ff7e1abfdffbdf 0xf4bfefc357fbff7b 0xfdfffe3fffffffff 0xffbfffc7ffffffff

def z76 : W := mkw 0x0002020083021081 0x0000404010604210 0xd80606038302739d 0xfb00c0c070604e73

def z77 : W := mkw 0x0200025011b41504 0x2040004a023682a0 0x0800000003fc0000 0x01000000007f8000

def z78 : W := mkw 0x24025210bbdff18f 0xa4804a42177bfe31 0xd8163633fffff39f 0xfb02c6c67ffffe73

def z79 : W := mkw 0x60025250a36eb5a9 0xac004a4a146dd6b5 0xd8163633e3ffffff 0xfb02c6c67c7fffff

def z80 : W := mkw 0x000081a540000000 0x00001034a8000000 0x020003f1e0000000 0x0040007e3c000000

def z81 : W := mkw 0x800000000c014a52 0x500000000180294a 0x000000001c03ffff 0x0000000003807fff

def z82 : W := mkw 0x23321370b3be358d 0x2466426e1677c6b1 0xda3637f3e3fe739d 0xfb46c6fe7c7fce73

def z83 : W := mkw 0x81fdadaf48014052 0x103fb5b5e900280a 0xf7ffffffe003e0f8 0xfefffffffc007c1f

def z84 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z85 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xadfbf0001ffd8002 0x15bf7e0003ffb000

def z86 : W := mkw 0x0000000000000000 0x0000000000000000 0xd0163633e0000000 0xfa02c6c67c000000

def z87 : W := mkw 0x41fdedef40608420 0x883fbdbde80c1084 0x27e9c9cc00e18c62 0x04fd3939801c318c

def z88 : W := mkw 0x0331a3f551b41504 0x2066347eaa3682a0 0x8e33f3f1e3fc0000 0x11c67e7e3c7f8000

def z89 : W := mkw 0x0000000000000000 0x0000000000000000 0xd0163633e002739d 0xfa02c6c67c004e73

def z90 : W := mkw 0x048f70000a4be003 0x8091ee0001497c00 0x040ff0000003e000 0x2081fe0000007c00

def z91 : W := mkw 0x0132400012d28005 0x80264800025a5000 0xfdfbc0001fff8007 0x3fbf780003fff000

def z92 : W := mkw 0x20021000a20a2089 0x0400420014414411 0x0000000000026098 0x0000000000004c13

def z93 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x88123231e31e739d 0x110246463c63ce73

def z94 : W := mkw 0x400082c5812014a0 0x08001058b0240294 0x02000bcd80001ce0 0xc0400179b000039c

def z95 : W := mkw 0x808c000a08014052 0x101180014100280a 0x500c040e0003f3fd 0xea018081c0007e7f

def z96 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0x8e23c3c183e00000 0x11c47878307c0000

def z97 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xbe2bcbcd83ffffff 0xf7c57979b07fffff

def z98 : W := mkw 0x22021250b7be3f8d 0x6440424a16f7c7f1 0x080000001ffe7f9f 0x0100000003ffcff3

def z99 : W := mkw 0x4332c3f593f695a5 0xa866587eb27ed2b4 0x8e33c3f183fc0000 0x11c6787e307f8000

def z100 : W := mkw 0xc08ec08f8a43c0f3 0x9811d811f148781e 0x040fc00f8003e0f8 0xa081f801f0007c1f

def z101 : W := mkw 0x03fdadef54b00e04 0x407fb5bdea9601c0 0x27e9c9cc1ce00c02 0x04fd3939839c0180

def z102 : W := mkw 0x01700f6001201400 0x002e01ec00240280 0xfbf00ff003e01c03 0x5f7e01fe007c0380

def z103 : W := mkw 0x00cc0c0a00000000 0x0019818140000000 0x71cc0c0e00000000 0xee398181c0000000

def z104 : W := mkw 0x41fdedef40608420 0x883fbdbde80c1084 0xf7ffffffe0e18c62 0xfefffffffc1c318c

def z105 : W := mkw 0xc0cccccf0c61ce72 0xd8199999e18c39ce 0x77edcdce1ce3ffff 0xeefdb9b9c39c7fff

def z106 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xa7fbfbfde0000000 0x14ff7f7fbc000000

def z107 : W := mkw 0x0330025015b41f04 0x6066004a02b683e0 0xf9f000001ffc1f07 0x1f3e000003ff83e0

def z108 : W := mkw 0x01bd200010900004 0x0037a40002120000 0xfdfff0001ffc0007 0x3fbffe0003ff8000

def z109 : W := mkw 0x03fdafff55b41f04 0x607fb5ffeab683e0 0xfffffffffffc1f07 0xffffffffffff83e0

def z110 : W := mkw 0x0000808500000000 0x00001010a0000000 0x2629c9cc00000000 0x04c5393980000000

def z111 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x08000000031e739d 0x010000000063ce73

def z112 : W := mkw 0x00cdadaf40000000 0x0019b5b5e8000000 0x060fffffe0000000 0xe0c1fffffc000000

def z113 : W := mkw 0x0000024001201400 0x0000004800240280 0xba280bcc03e39ce3 0xf7450179807c739c

def z114 : W := mkw 0x01bda1a540000000 0x0037b434a8000000 0xf7fff3f1e0000000 0x3efffe7e3c000000

def z115 : W := mkw 0xc0cececf8f63def3 0xd819d9d9f1ec7bde 0xbfebcbcd9fe39ce3 0xf7fd7979b3fc739c

def z116 : W := mkw 0x048f70001adbe007 0x8091ee00035b7c00 0x0c0ff0001fffe007 0x2181fe0003fffc00

def z117 : W := mkw 0x02400f7015b41f04 0x604801ee02b683e0 0x0a000ff01ffc1f07 0x414001fe03ff83e0

def z118 : W := mkw 0x20021010a20e2189 0x240042021441c431 0x40163433e01e639c 0xa802c6867c03cc73

def z119 : W := mkw 0x0000020081001080 0x0000004010200210 0x0000020180001080 0xc000004030000210

def z120 : W := mkw 0x0000000000000000 0x0000000000000000 0x400404020000631c 0x0800808040000c63

def z121 : W := mkw 0x41bfe2c5836294a1 0x8837fc58b06c5294 0xfffffbcd83e39ce3 0xffffff79b07c739c

def z122 : W := mkw 0x0130000010900004 0x0026000002120000 0x21e000001ce00002 0x043c0000039c0000

def z123 : W := mkw 0x25bf3210bb9f718f 0x24b7e6421773ee31 0xd9d63633ff1e739d 0xfb3ac6c67fe3ce73

def z124 : W := mkw 0x03700f3015941b04 0x606e01e602b28360 0xd9d006301f1c1305 0x5b3a00c603e38260

def z125 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0xf1de3e3ffc03ffff 0xfe3bc7c7ff807fff

def z126 : W := mkw 0x4000404000608420 0x88000808000c1084 0x0000000000e18c62 0x00000000001c318c

def z127 : W := mkw 0x23721f30b79e3b8d 0x646e43e616f3c771 0xd9d63633ff1e739d 0xfb3ac6c67fe3ce73

def z128 : W := mkw 0x01fd2d2a40000000 0x003fa5a548000000 0x01c0000000000000 0x0038000000000000

def z129 : W := mkw 0x25bf70103adfe10f 0xa4b7ee02075bfc21 0xfdfff4327fffe31f 0x3fbffe864ffffc63

def z130 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xae2bcbcd83e18c62 0x15c57979b07c318c

def z131 : W := mkw 0x80cc0e1a0d055b52 0x701981c341a0ab6a 0xf9dc0e3e1f1fffff 0xff3b81c7c3e3ffff

def z132 : W := mkw 0x008c000008014002 0x0011800001002800 0x21c800001c018002 0x0439000003803000

def z133 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x88123231e31c0000 0x110246463c638000

def z134 : W := mkw 0x008da08f40000000 0x0011b411e8000000 0x040ff00fe0000000 0xa081fe01fc000000

def z135 : W := mkw 0x40024240836294a1 0x88004848106c5294 0x0800000003e39ce3 0x01000000007c739c

def z136 : W := mkw 0x0002424003629401 0x80004848006c5280 0xbe2bcbc003e39c03 0x77c57978007c7380

def z137 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x41c40c0e1c007ffc 0xc8388181c3800fff

def z138 : W := mkw 0x820002501db55f56 0x7040004a03b6abea 0x080000001fffffff 0x0100000003ffffff

def z139 : W := mkw 0x05bd600018d1c006 0x80b7ac00031a3800 0x25e9c0001ce18002 0x04bd3800039c3000

def z140 : W := mkw 0x0330037011b41504 0x2066006e023682a0 0xfbf003f01ffc0007 0x1f7e007e03ff8000

def z141 : W := mkw 0x80400c0a04000a50 0x500801814080014a 0x00000c0e00001ff8 0xc0000181c00003ff

def z142 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x01c000001c000000 0x0038000003800000

def z143 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7fffffffc018c62 0xfeffffffff80318c

def z144 : W := mkw 0x0533700012daa005 0x80a66e00025b5400 0xbc3bf00003ff8003 0x37877e00007ff000

def z145 : W := mkw 0xa0ce1e1aaf0f7bdb 0x7419c3c355e1ef7b 0x79cc0c0e1f1fffff 0xef398181c3e3ffff

def z146 : W := mkw 0x47fffff59fffffa7 0xe8fffffeb3fffff4 0xfffffffd9fffffe7 0xffffffffb3fffffc

def z147 : W := mkw 0x21fdbdbf600c2108 0x243fb7b7ec018421 0xf7ffffffe01c631c 0xfefffffffc038c63

def z148 : W := mkw 0x0000000000000000 0x0000000000000000 0x80123231e0000000 0x100246463c000000

def z149 : W := mkw 0x25337210b3deb18d 0xa4a66e42167bd631 0x8c33f231e3fc0000 0x11867e463c7f8000

def z150 : W := mkw 0x0000000000000000 0x0000000000000000 0x3008080c00039ce3 0xe60101018000739c

def z151 : W := mkw 0x040250001adbe007 0x80804a00035b7c00 0xbc2bc0001fffe007 0x3785780003fffc00

def z152 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0x27eff9cfe0000000 0xa4fdff39fc000000

def z153 : W := mkw 0x61ffffffe36eb5a9 0xac3ffffffc6dd6b5 0xffffffffe3ffffff 0xfffffffffc7fffff

def z154 : W := mkw 0x40024240836294a1 0x88004848106c5294 0xba200bc003e39ce3 0x57440178007c739c

def z155 : W := mkw 0x80408daf44000a50 0x500811b5e880014a 0x02000fffe0001ff8 0xc04001fffc0003ff

def z156 : W := mkw 0x05fffdaf4a4be003 0x80bfffb5e9497c00 0xf7ffffffe003e000 0xfefffffffc007c00

def z157 : W := mkw 0x0002000082020081 0x0000400010404010 0x0002000180020080 0xa000400030004010

def z158 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x21c8080c1c03ffff 0x0439010183807fff

def z159 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x98020201831e739d 0xf30040403063ce73

def z160 : W := mkw 0x03fc0f7a15b41f04 0x607f81ef42b683e0 0xfbfc0ffe1ffc1f07 0xff7f81ffc3ff83e0

def z161 : W := mkw 0x0000808500000000 0x00001010a0000000 0xb62bcbcd80039ce3 0xf6c57979b000739c

def z162 : W := mkw 0x4133e3e5c36294a1 0x88267c7cb86c5294 0xbe3bfbfde3e39ce3 0xf7c77f7fbc7c739c

def z163 : W := mkw 0x01700d2000000000 0x002e01a400000000 0xf3f00ff000000000 0x5e7e01fe00000000

def z164 : W := mkw 0x048ff08f4a4be003 0x8091fe11e9497c00 0x040ff00fe003e000 0xa081fe01fc007c00

def z165 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000000002739d 0x0000000000004e73

def z166 : W := mkw 0x0000808500000000 0x00001010a0000000 0xb62bcbcd80000000 0xf6c57979b0000000

def z167 : W := mkw 0x41ffefefc36294a1 0x883ffdfdf86c5294 0xffffffffe3e39ce3 0xfffffffffc7c739c

def z168 : W := mkw 0x808da08f48014052 0x1011b411e900280a 0x040ff00fe003e0f8 0xa081fe01fc007c1f

def z169 : W := mkw 0x07ff7f701fffff07 0xe0ffefee03ffffe0 0xfffffff01fffff07 0x7ffffffe03ffffe0

def z170 : W := mkw 0x4002c085824280a1 0x88005810b0485014 0x0403c00180000000 0x0080780030000000

def z171 : W := mkw 0x0002020083021081 0x0000404010604210 0xd8163633e3021081 0xfb02c6c67c604210

def z172 : W := mkw 0x00400e4005201e00 0x400801c800a403c0 0xfbe00fc01fe01f07 0x5f7c01f803fc03e0

def z173 : W := mkw 0x0200004014b00e04 0x40400008029601c0 0x000000001ce00c02 0x00000000039c0180

def z174 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0x2de9c0001fffe007 0x05bd380003fffc00

def z175 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x08000000031c0000 0x0100000000638000

def z176 : W := mkw 0xa3fe1f7abfbf7fdf 0x747fc3ef57f7effb 0xfbfe3fffffffffff 0xff7fc7ffffffffff

def z177 : W := mkw 0x20021200a30a3089 0x0400424014614611 0x98063203e3027099 0xf300c6407c604e13

def z178 : W := mkw 0x0000000000000000 0x0000000000000000 0x0008000c000380e0 0xa00100018000701c

def z179 : W := mkw 0x05fffdaf5adbe007 0x80bfffb5eb5b7c00 0xffffffffffffe007 0xfffffffffffffc00

def z180 : W := mkw 0x20001210a10c3188 0x2400024214218631 0x40143633e01c739c 0xc80286c67c038e73

def z181 : W := mkw 0x45bff2c59bfbf4a7 0x88b7fe58b37f7e94 0xfffffbcd9ffffce7 0xffffff79b3ffff9c

def z182 : W := mkw 0x83fc0d6a1cb14e56 0x507f81ad439629ca 0x23e809cc1ce18c62 0x047d0139839c318c

def z183 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x21cc080e1c03ecfa 0xa4398101c3807d9f

def z184 : W := mkw 0x00400c0004000a00 0x4008018000800140 0x21c008001c000c02 0x0438010003800180

def z185 : W := mkw 0x0531600010d08004 0x80a62c00021a1000 0x0421c00000e00000 0x00843800001c0000

def z186 : W := mkw 0x85fd3c0a1c996a56 0x50bfa78143932d4a 0x41d434021c1c631c 0x083a868043838c63

def z187 : W := mkw 0xc042cecf87629ef1 0xd80859d9f0ec53de 0xbe2bcfcf83e39ffb 0xf7c579f9f07c73ff

def z188 : W := mkw 0x0000000000000000 0x0000000000000000 0x700c0c0e0003ffff 0xee018181c0007fff

def z189 : W := mkw 0x0200025005241f00 0x6040004a00a483e0 0x0000000000001f00 0x00000000000003e0

def z190 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xd8163633e31c0000 0xfb02c6c67c638000

def z191 : W := mkw 0x20000210a1041188 0x2400004214208231 0xd8100633e31c139d 0xdb0200c67c638273

def z192 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7ffffffe002739d 0xfefffffffc004e73

def z193 : W := mkw 0x05fd3d2a58996006 0x00bfa7a54b132c00 0x41d434327c1c6004 0x083a86864f838c00

def z194 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0x27e9c9cc1c018c62 0x04fd39398380318c

def z195 : W := mkw 0x0002400002428001 0x8000480000485000 0x040bc00000038000 0x2081780000007000

def z196 : W := mkw 0x20025210a34eb189 0xa4004a421469d631 0xfc3ff633e3fff39f 0xff87fec67c7ffe73

def z197 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xbe3bfbfde3ff9ce3 0xf7c77f7fbc7ff39c

def z198 : W := mkw 0x0000000000000000 0x0000000000000000 0xd8100000031c0005 0x1b02000000638000

def z199 : W := mkw 0x80ce0e0a8f035ad3 0x5019c1c151e06b5a 0xf9ce0e0f9f03ffff 0xff39c1c1f3e07fff

def z200 : W := mkw 0x0000000000000000 0x0000000000000000 0x4014343260000000 0x080286864c000000

def z201 : W := mkw 0x05ff7c0a1adbe007 0x80bfef81435b7c00 0xfdfffc0e1fffe007 0xffbfff81c3fffc00

def z202 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0x0621c1c000e00000 0x00c43838001c0000

def z203 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x41c404021c03ffff 0x0838808043807fff

def z204 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x00063633e0027398 0xe000c6c67c004e73

def z205 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0x45dff43fe0000000 0xa8bbfe87fc000000

def z206 : W := mkw 0x85fd6c0a1cd1ca56 0xd0bfad81439a394a 0x75edcc0e1ce3ffff 0xeebdb981c39c7fff

def z207 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xb7ebcbcd80000000 0xf6fd7979b0000000

def z208 : W := mkw 0x01700d2010900004 0x002e01a402120000 0xfbf00ff01ffc0007 0x5f7e01fe03ff8000

def z209 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf80ffc1fff9fe7 0xff7f01ff83fff3fc

def z210 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x08063003e31e739d 0xa100c6007c63ce73

def z211 : W := mkw 0x02400f7005241f00 0x604801ee00a483e0 0x02000ff000001f00 0x404001fe000003e0

def z212 : W := mkw 0x01fdadaf44000a00 0x403fb5b5e8800140 0xf7fffffffc001f07 0xfeffffffff8003e0

def z213 : W := mkw 0x4002d2c5836ab4a1 0x88005a58b06d5694 0xfe3ffbcd83fffce7 0xffc7ff79b07fff9c

def z214 : W := mkw 0x05ff7d2a5adbe007 0x80bfefa54b5b7c00 0xfdfff4327fffe007 0x3fbffe864ffffc00

def z215 : W := mkw 0x82400f7a05241f50 0x704801ef40a483ea 0x02000ffe00001ff8 0xc04001ffc00003ff

def z216 : W := mkw 0x0171ada540000000 0x002e35b4a8000000 0xf7f3fff1e0000000 0x5efe7ffe3c000000

def z217 : W := mkw 0x85bf700a1adbe057 0x90b7ee01435b7c0a 0xfdfff00e1fffe0ff 0xbfbffe01c3fffc1f

def z218 : W := mkw 0x05fffdaf5adbe007 0x80bfffb5eb5b7c00 0xfffff9cc1fffe007 0x3fffff3983fffc00

def z219 : W := mkw 0x05bd600018d1c006 0x80b7ac00031a3800 0xf5fff0001ce18002 0x3ebffe00039c3000

def z220 : W := mkw 0x4132c2c593f294a5 0x88265858b27e5294 0xfffbcbcd9fff9ce7 0xffff7979b3fff39c

def z221 : W := mkw 0x6002d085a24aa0a9 0x8c005a10b4495415 0x040ff00fe003e0f8 0xa081fe01fc007c1f

def z222 : W := mkw 0x21bf3210a30e3189 0x2437e6421461c631 0xfdfff633e31e739d 0xffbffec67c63ce73

def z223 : W := mkw 0x82cc0f7a0d255f52 0x705981ef41a4abea 0x73cc0ffe1c03ffff 0xee7981ffc3807fff

def z224 : W := mkw 0x0000000000000000 0x0000000000000000 0x0004000200026098 0xa000800040004c13

def z225 : W := mkw 0x600292d5a32e35a9 0x2c00525ab465c6b5 0xda163fffe31e7ffd 0xfb42c7fffc63cfff

def z226 : W := mkw 0x02400f7005241f00 0x604801ee00a483e0 0x73c00ff01c001f07 0x4e7801fe038003e0

def z227 : W := mkw 0x25bf7210bbdff18f 0xa4b7ee42177bfe31 0xfdfff231ffffe007 0x3fbffe463ffffc00

def z228 : W := mkw 0x01fd2d2a40000000 0x003fa5a548000000 0x71dc3c3e60000000 0xee3b8787cc000000

def z229 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0xb62bcbcd80e18c62 0xf6c57979b01c318c

def z230 : W := mkw 0x20000000a0000088 0x0400000014000011 0x00000003e0000098 0x800000007c000013

def z231 : W := mkw 0x03700d6014b00e04 0x406e01ac029601c0 0xfbf009c01ffc0c07 0x1f7e013803ff8180

def z232 : W := mkw 0x6002c2d5a36695a9 0xac00585ab46cd2b5 0xbe2bcfffe3e39ffb 0xf7c579fffc7c73ff

def z233 : W := mkw 0x03fc0f701db55f06 0x607f81ee03b6abe0 0xfbfc0ff01fffff07 0x7f7f81fe03ffffe0

def z234 : W := mkw 0xc0cccccf0c61ce72 0xd8199999e18c39ce 0x27e9c9cc1ce18c62 0x04fd3939839c318c

def z235 : W := mkw 0x0000000000000000 0x0000000000000000 0x5000040000001305 0x4a00008000000260

def z236 : W := mkw 0x00021000020a2001 0x0000420000414400 0x88123000031c0000 0x1102460000638000

def z237 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xfe2fcfcf83e3ffff 0xffc5f9f9f07c7fff

def z238 : W := mkw 0x01700d2004000a00 0x402e01a400800140 0xf3f00ff01c001f07 0x5e7e01fe038003e0

def z239 : W := mkw 0x4002c0c5826284a1 0x88005818b04c5094 0x262bc9cd80e38ce2 0xa4c57939b01c719c

def z240 : W := mkw 0x20000210a1041188 0x2400004214208231 0x00000633e0001398 0xc00000c67c000273

def z241 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf40ff21ffe7f9f 0xff7e81fe43ffcff3

def z242 : W := mkw 0x4370cff515f49f24 0xe86e19fea2be93e4 0xfff9cffc1ffd9f67 0x5fff39ff83ffb3ec

def z243 : W := mkw 0x23ffbffff7be3f8d 0x647ff7fffef7c7f1 0xfffffffffffe7f9f 0xffffffffffffcff3

def z244 : W := mkw 0xa0cc0e1aad055bda 0x741981c355a0ab7b 0x71cc0e3ffc03ffff 0xee3981c7ff807fff

def z245 : W := mkw 0x20408fbfe1041188 0x240811f7fc208231 0x02000fffe0001398 0xc04001fffc000273

def z246 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x71cc0c0e1c018c62 0xee398181c380318c

def z247 : W := mkw 0x45bfe2c59bf3d4a7 0x88b7fc58b37e7a94 0xbfebcbcd9fe39ce3 0xf7fd7979b3fc739c

def z248 : W := mkw 0x00cc0c0a00000000 0x0019818140000000 0x21c8080c00000000 0x0439010180000000

def z249 : W := mkw 0x0130000010900004 0x0026000002120000 0x8830000003fc0000 0x11060000007f8000

def z250 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0x23e00ff01ce01f02 0x447c01fe039c03e0

def z251 : W := mkw 0x0000000000000000 0x0000000000000000 0x2008080c00018c62 0x040101018000318c

def z252 : W := mkw 0x0000021001041100 0x2000004200208220 0x08000000031c1305 0x0100000000638260

def z253 : W := mkw 0x85bf70001edbea57 0xd0b7ee0003db7d4a 0xfdfff0001fffffff 0x3fbffe0003ffffff

def z254 : W := mkw 0x0000000000000000 0x0000000000000000 0x3008000000038003 0x2601000000007000

def z255 : W := mkw 0x40408fefc12014a0 0x080811fdf8240294 0x02000fffe0001ce0 0xc04001fffc00039c

def z256 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xc8163633e31c631c 0x1902c6c67c638c63

def z257 : W := mkw 0x03fd2d3a54940b04 0x607fa5a74a928160 0x41d434327c1c0304 0x083a86864f838060

def z258 : W := mkw 0x00400c0004000a00 0x4008018000800140 0x71c40c021c027f9f 0xee38818043804ff3

def z259 : W := mkw 0x4202425097f69fa5 0xe840484a12fed3f4 0x080000001fff9fe7 0x0100000003fff3fc

def z260 : W := mkw 0xa08e121aab0f71db 0x3411c2435561ee3b 0xd81e363fe31ff3fd 0xfb03c6c7fc63fe7f

def z261 : W := mkw 0x00021200830a3081 0x0000424010614610 0xd8163201831e7085 0xfb02c6403063ce10

def z262 : W := mkw 0x80cdac8f4c014a52 0x5019b591e980294a 0x75cffc0ffc03ffff 0xeeb9ff81ff807fff

def z263 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x51c404021c02739d 0xea38808043804e73

def z264 : W := mkw 0x01fd2d2a40000000 0x003fa5a548000000 0x41d4343260000000 0x083a86864c000000

def z265 : W := mkw 0x20ce1e1aa30e3189 0x2419c3c35461c631 0xf9de3e3fe31e739d 0xff3bc7c7fc63ce73

def z266 : W := mkw 0x05bd600018d1c006 0x80b7ac00031a3800 0xfdf9c0001ffd8007 0x1fbf380003ffb000

def z267 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x21c80c0e1c019ffa 0xc4390181c38033ff

def z268 : W := mkw 0x00408daf40000000 0x000811b5e8000000 0xd2163fffe0000000 0xfa42c7fffc000000

def z269 : W := mkw 0x0002400002428001 0x8000480000485000 0xbc2bc00003e38003 0x37857800007c7000

def z270 : W := mkw 0x40cececf836294a1 0x8819d9d9f06c5294 0xffefcfcf83e39ce3 0xfffdf9f9f07c739c

def z271 : W := mkw 0x22421f70a72e3f89 0x644843ee14e5c7f1 0xda163ff3e31e7f9d 0xfb42c7fe7c63cff3

def z272 : W := mkw 0x21ff3f3ae30e3189 0x243fe7e75c61c631 0xd9d63633e31e739d 0xfb3ac6c67c63ce73

def z273 : W := mkw 0x0001a08540000000 0x00003410a8000000 0x0403f001e0000000 0x00807e003c000000

def z274 : W := mkw 0x0002021083061181 0x200040421060c230 0xd8120631831e1385 0xfb0240c63063c270

def z275 : W := mkw 0x80400c0a04000a50 0x500801814080014a 0x0000040200000318 0x0000008040000063

def z276 : W := mkw 0x008da08f40000000 0x0011b411e8000000 0x0409c00c00000000 0x0081380180000000

def z277 : W := mkw 0x83fc0d6a1cb14e56 0x507f81ad439629ca 0x73ec0dce1ce3ffff 0xee7d81b9c39c7fff

def z278 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0x27e9cfffe0000000 0xc4fd39fffc000000

def z279 : W := mkw 0x01fd2d2a40000000 0x003fa5a548000000 0xd1d63633e0000000 0xfa3ac6c67c000000

def z280 : W := mkw 0xc1ffefefcf63def3 0xd83ffdfdf9ec7bde 0xffffffffffe3ffff 0xfffffffffffc7fff

def z281 : W := mkw 0x03fd2f7a55b41f04 0x607fa5ef4ab683e0 0xfbf43ff27ffc1f07 0x5f7e87fe4fff83e0

def z282 : W := mkw 0x05bf700012daa005 0x80b7ee00025b5400 0xfdfff00003fc0000 0x3fbffe00007f8000

def z283 : W := mkw 0x0000000000000000 0x0000000000000000 0x5004040200000000 0xea00808040000000

def z284 : W := mkw 0x03700d3014940b04 0x606e01a602928160 0xf3f00ff01c1c0304 0x5e7e01fe03838060

def z285 : W := mkw 0x03fdadbf54940b04 0x607fb5b7ea928160 0xf7fffffffc1c0304 0xfeffffffff838060

def z286 : W := mkw 0x01bc000018914006 0x0037800003122800 0xf9fc00001fffe007 0x3f3f800003fffc00

def z287 : W := mkw 0x0000100000082000 0x0000020000010400 0x40143000001c6004 0x0802860000038c00

def z288 : W := mkw 0x05bd200018914006 0x00b7a40003122800 0x01c000001c000000 0x0038000003800000

def z289 : W := mkw 0x85fffdaf5edbea57 0xd0bfffb5ebdb7d4a 0xffffffffffffffff 0xffffffffffffffff

def z290 : W := mkw 0x85fd3c0a1c996a56 0x50bfa78143932d4a 0x71dc3c0e1c1fffff 0xee3b8781c383ffff

def z291 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xf81e3e3fe31fffff 0xff03c7c7fc63ffff

def z292 : W := mkw 0x05bff1a55adbe007 0x80b7fe34ab5b7c00 0xfffff3f1ffffe007 0x3ffffe7e3ffffc00

def z293 : W := mkw 0x87ff7f7a1fffff57 0xf0ffefef43ffffea 0xfffffffe1fffffff 0xffffffffc3ffffff

def z294 : W := mkw 0x02400d6004200e00 0x404801ac008401c0 0x020009c000000c00 0x0040013800000180

def z295 : W := mkw 0x01ffafafc3021081 0x003ff5f5f8604210 0xffffffffe3021081 0xfffffffffc604210

def z296 : W := mkw 0x65bff2d5bbfff5af 0xacb7fe5ab77ffeb5 0xffffffffffffffff 0xffffffffffffffff

def z297 : W := mkw 0x400080c500200420 0x08001018a0040084 0x020009cc00000c60 0x004001398000018c

def z298 : W := mkw 0x440252409bfbf4a7 0x88804a48137f7e94 0x080000001ffffce7 0x0100000003ffff9c

def z299 : W := mkw 0x00400e1005041b00 0x600801c200a08360 0xf9d00e301f1c1f07 0x5f3a01c603e383e0

def z300 : W := mkw 0x4042cfefc36294a1 0x880859fdf86c5294 0xbe2bcfffe3e39ce3 0xf7c579fffc7c739c

def z301 : W := mkw 0x02400e5015b41f04 0x604801ca02b683e0 0x79c00c001ffc1f07 0x4f38018003ff83e0

def z302 : W := mkw 0x01bd200000000000 0x0037a40000000000 0x41d4300000000000 0x083a860000000000

def z303 : W := mkw 0x0400400018d1c006 0x80800800031a3800 0x000000001ce18002 0x00000000039c3000

def z304 : W := mkw 0x0000001000040100 0x2000000200008020 0x40100430001c0304 0x0802008600038060

def z305 : W := mkw 0x008d200a40000000 0x0011a40148000000 0x0004300260000000 0x000086004c000000

def z306 : W := mkw 0x0171adaf40000000 0x002e35b5e8000000 0x8633ffffe0000000 0xd0c67ffffc000000

def z307 : W := mkw 0x05fffdaf52daa005 0x80bfffb5ea5b5400 0xffffffffe3fc0000 0xfffffffffc7f8000

def z308 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xc7f7f7f3e0000000 0x18fefefe7c000000

def z309 : W := mkw 0x01708da500000000 0x002e11b4a0000000 0xf7fbcffd80000000 0xfeff79ffb0000000

def z310 : W := mkw 0x800000000c014a52 0x500000000180294a 0x3008080c1c03ffff 0xe601010183807fff

def z311 : W := mkw 0x00408daf40000000 0x000811b5e8000000 0xb62bcfffe0000000 0xf6c579fffc000000

def z312 : W := mkw 0x0130000010900004 0x0026000002120000 0x41d000001c1c0004 0x083a000003838000

def z313 : W := mkw 0x20021010220e2109 0x240042020441c421 0xd8163432631e631d 0x3b02c6864c63cc63

def z314 : W := mkw 0x85fd6c0a1cd1ca56 0xd0bfad81439a394a 0x25e9c80c1ce18c62 0x04bd3901839c318c

def z315 : W := mkw 0x4533f2c593fab4a5 0x88a67e58b27f5694 0xbe3bfbcd83ff9ce3 0xf7c77f79b07ff39c

def z316 : W := mkw 0x208fb29fe30e3189 0x2411f653fc61c631 0xdc1ff63fe31e739d 0xfb83fec7fc63ce73

def z317 : W := mkw 0x00cc0c0a00000000 0x0019818140000000 0x71cc0c0e0002739d 0xee398181c0004e73

def z318 : W := mkw 0x4000c2c501609420 0x88001858a02c1284 0xbe29cbcc03e19c63 0x57c53979807c338c

def z319 : W := mkw 0x0002024083221481 0x0000404810644290 0xba220bc183e21c83 0xf7444178307c4390

def z320 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xfe3fffffe3e39ce3 0xffc7fffffc7c739c

def z321 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0x2e29c9cc03e39ce3 0x05c53939807c739c

def z322 : W := mkw 0x01fdadaf50900004 0x003fb5b5ea120000 0xfffffffffffc0007 0xffffffffffff8000

def z323 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x41cc040e1c03e3fc 0xa8398081c3807c7f

def z324 : W := mkw 0x05fdedaf58d1c006 0x80bfbdb5eb1a3800 0xf7fffffffce18002 0xfeffffffff9c3000

def z325 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000080c00001ce0 0xc00001018000039c

def z326 : W := mkw 0x060252501fffff07 0xe0c04a4a03ffffe0 0x080000001fffff07 0x0100000003ffffe0

def z327 : W := mkw 0x00400c0004000a00 0x4008018000800140 0x00000c0000001f00 0x40000180000003e0

def z328 : W := mkw 0x00cc8c8f00000000 0x00199191e0000000 0xf7efcfcf80000000 0xfefdf9f9f0000000

def z329 : W := mkw 0x0000000000000000 0x0000000000000000 0xd016300000000000 0x3a02c60000000000

def z330 : W := mkw 0x01700d2000000000 0x002e01a400000000 0xf3f63ff3e0000000 0xfe7ec7fe7c000000

def z331 : W := mkw 0x0000021001041100 0x2000004200208220 0xd8140632031e739d 0xfb0280c64063ce73

def z332 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf63ff3fffc1f07 0xff7ec7fe7fff83e0

def z333 : W := mkw 0x01fdafbf41041100 0x203fb5f7e8208220 0xffffffffe31c1305 0xfffffffffc638260

def z334 : W := mkw 0x03724f7017f69f05 0xe06e49ee02fed3e0 0xfffbcff01fff9f07 0x7fff79fe03fff3e0

def z335 : W := mkw 0x41fdafefc12014a0 0x083fb5fdf8240294 0xf7ffffffe0001ce0 0xfefffffffc00039c

def z336 : W := mkw 0x0000024001201400 0x0000004800240280 0x0800000003e01c03 0x01000000007c0380

def z337 : W := mkw 0x0533700012daa005 0x80a66e00025b5400 0xfdf3f0001ffc0007 0x1fbe7e0003ff8000

def z338 : W := mkw 0x80cc0c0a04000a50 0x501981814080014a 0x71cc0c0e00001ff8 0xee398181c00003ff

def z339 : W := mkw 0x20001010200c2108 0x2400020204018421 0xd0163633e01c631c 0xfa02c6c67c038c63

def z340 : W := mkw 0xc0408ecf85201ef0 0x580811d9f0a403de 0x02000fcf80001ff8 0xc04001f9f00003ff

def z341 : W := mkw 0x43ffefffd7f69fa5 0xe87ffdfffafed3f4 0xffffffffffff9fe7 0xfffffffffffff3fc

def z342 : W := mkw 0x01bd200000000000 0x0037a40000000000 0x25e9c00000000000 0x04bd380000000000

def z343 : W := mkw 0x05fdedaf58d1c006 0x80bfbdb5eb1a3800 0x27e9c9cc1ce18002 0x04fd3939839c3000

def z344 : W := mkw 0x0000004000200400 0x0000000800040080 0x222009c000e00c02 0x04440138001c0180

def z345 : W := mkw 0x0000024001201400 0x0000004800240280 0x8a2003c003e00000 0x11440078007c0000

def z346 : W := mkw 0x40024240836294a1 0x88004848106c5294 0x9802020183e39ce3 0xf3004040307c739c

def z347 : W := mkw 0xc0cc8ecf8d215ef2 0x581991d9f1a42bde 0x73cc0fcf9c03ffff 0xee7981f9f3807fff

def z348 : W := mkw 0x4002c085824280a1 0x88005810b0485014 0x340bc80d80039ce3 0xe6817901b000739c

def z349 : W := mkw 0x208fb08fe20a2089 0x0411f611fc414411 0x040ff00fe0026098 0xa081fe01fc004c13

def z350 : W := mkw 0x03fdafff51b41504 0x207fb5ffea3682a0 0xffffffffe3fc0000 0xfffffffffc7f8000

def z351 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xd8163000031e739d 0x3b02c6000063ce73

def z352 : W := mkw 0x81fd2d2a4c014a52 0x503fa5a54980294a 0x71dc3c3e7c03ffff 0xee3b8787cf807fff

def z353 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0x8c3ff00003ffe000 0x3187fe00007ffc00

def z354 : W := mkw 0x0402500012daa005 0x80804a00025b5400 0x0800000003fc0000 0x01000000007f8000

def z355 : W := mkw 0x20001210210c3108 0x2400024204218621 0xd8143632631c731d 0x5b0286c64c638e63

def z356 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x61cc0c0e1c01ef7e 0x0c398181c3803def

def z357 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0x2be009c01ffc1f07 0x057c013803ff83e0

def z358 : W := mkw 0x008c000008014002 0x0011800001002800 0x71cc080c1c03fce7 0xee39810183807f9c

def z359 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0xd637f7f3e0000000 0xfac6fefe7c000000

def z360 : W := mkw 0x00cc0c000c014a02 0x4019818001802940 0x71cc0c001c03ff07 0x6e39818003807fe0

def z361 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0xb63bfbfde0000000 0xf6c77f7fbc000000

def z362 : W := mkw 0x808c000a08014052 0x101180014100280a 0x71cc000e1c03e0ff 0xae398001c3807c1f

def z363 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0x43d00ff01c1c1f04 0x487a01fe038383e0

def z364 : W := mkw 0x4000c2c5816094a0 0x88001858b02c1294 0x2629cbcd80e19ce2 0xc4c53979b01c339c

def z365 : W := mkw 0x83700f7a15b41f54 0x706e01ef42b683ea 0xfbf00ffe1ffc1fff 0xdf7e01ffc3ff83ff

def z366 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0x8e33f3f1e3fc0000 0x11c67e7e3c7f8000

def z367 : W := mkw 0x45bff2c59bfbf4a7 0x88b7fe58b37f7e94 0xfffff3c19fffe007 0x3ffffe7833fffc00

def z368 : W := mkw 0x0000000000000000 0x0000000000000000 0xb42bc00000000000 0x3685780000000000

def z369 : W := mkw 0x45bf72409bfbf4a7 0x88b7ee48137f7e94 0xfdfff0001ffffce7 0x3fbffe0003ffff9c

def z370 : W := mkw 0x40008085800000a0 0x08001010b0000014 0x0000000d800000e0 0x80000001b000001c

def z371 : W := mkw 0x008c000008014002 0x0011800001002800 0x41c400001c006004 0x0838800003800c00

def z372 : W := mkw 0x45ffffefdbfbf4a7 0x88bffffdfb7f7e94 0xfffffffffffffce7 0xffffffffffffff9c

def z373 : W := mkw 0x4002c0c502628421 0x88005818a04c5084 0xbe2bc9cc03e38c63 0x37c57939807c718c

def z374 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0x3629c9cc00e39ce3 0xe6c53939801c739c

def z375 : W := mkw 0x00021000020a2001 0x0000420000414400 0x08000000031e6005 0x010000000063cc00

def z376 : W := mkw 0x0000808500000000 0x00001010a0000000 0x8623c3c180000000 0x10c4787830000000

def z377 : W := mkw 0x600082d5a12415a8 0x2c00105ab42482b5 0x02000fffe0001ff8 0xc04001fffc0003ff

def z378 : W := mkw 0x4002c085824280a1 0x88005810b0485014 0xbc2bc00d83e380e3 0xb7857801b07c701c

def z379 : W := mkw 0x05fdbdaf58996006 0x00bfb7b5eb132c00 0xf7fffffffc1c6004 0xfeffffffff838c00

def z380 : W := mkw 0x23321370b3be358d 0x2466426e1677c6b1 0x8a3233f1e3fc0000 0x1146467e3c7f8000

def z381 : W := mkw 0x6002d2c5a36ab4a9 0x8c005a58b46d5695 0xbe2ffbcfe3e3fcfb 0xf7c5ff79fc7c7f9f

def z382 : W := mkw 0x4172cfe5836294a1 0x882e59fcb06c5294 0xfffbcffd83e39ce3 0xffff79ffb07c739c

def z383 : W := mkw 0x0000020001001000 0x0000004000200200 0x9800020003001001 0x5300004000600200

def z384 : W := mkw 0x0000000000000000 0x0000000000000000 0x3000080000001c03 0x4600010000000380

def z385 : W := mkw 0x4042cec587629ea1 0xc80859d8b0ec53d4 0xffebcfcd9fe39fe7 0xfffd79f9b3fc73fc

def z386 : W := mkw 0x0200025015b41f04 0x6040004a02b683e0 0xba200bc01ffc1f07 0x5744017803ff83e0

def z387 : W := mkw 0x0000000000000000 0x0000000000000000 0xb2200bc000000000 0x5644017800000000

def z388 : W := mkw 0xc0cecc8f8e43caf3 0xd819d991f1c8795e 0x75cfcc0f9c03ffff 0xeeb9f981f3807fff

def z389 : W := mkw 0x83fc0d3a1c954b56 0x707f81a74392a96a 0x41d404321c1c631c 0x083a808643838c63

def z390 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff4021ffff39f 0xffbffe8043fffe73

def z391 : W := mkw 0x0130012000000000 0x0026002400000000 0x823003f000000000 0x1046007e00000000

def z392 : W := mkw 0x248f7210ab4ff18b 0xa491ee421569fe31 0xdc1ff633e31ff39d 0xfb83fec67c63fe73

def z393 : W := mkw 0x0330016010b00404 0x0066002c02160080 0x022001c000e00000 0x00440038001c0000

def z394 : W := mkw 0x808c000a08014052 0x101180014100280a 0x0004000200006018 0x0000800040000c03

def z395 : W := mkw 0x07bf73701bfff507 0xa0f7ee6e037ffea0 0xfffff3f01fffe007 0x3ffffe7e03fffc00

def z396 : W := mkw 0x80400c0a04000a50 0x500801814080014a 0x0000080c00000c60 0x000001018000018c

def z397 : W := mkw 0x0002400002428001 0x8000480000485000 0x0800000003e38003 0x01000000007c7000

def z398 : W := mkw 0x2133b3b5e30e3189 0x24267676bc61c631 0xde37f7f3e31e739d 0xfbc6fefe7c63ce73

def z399 : W := mkw 0xc5fffecf9ffbfef7 0xd8bfffd9f3ff7fde 0xffffffcf9fffffff 0xfffffff9f3ffffff

def z400 : W := mkw 0x05bd300018996006 0x00b7a60003132c00 0xf9f430001ffc6007 0x1f3e860003ff8c00

def z401 : W := mkw 0xa0021210af0f7bdb 0x7400424215e1ef7b 0x080000001f1fffff 0x0100000003e3ffff

def z402 : W := mkw 0x80400c0a0c014a52 0x500801814180294a 0x00000c0e1c03ffff 0xc0000181c3807fff

def z403 : W := mkw 0x0200001014940b04 0x6040000202928160 0x000000001c1c0304 0x0000000003838060

def z404 : W := mkw 0x80cc8daf4c014a52 0x501991b5e980294a 0x73cc0ffffc03ffff 0xee7981ffff807fff

def z405 : W := mkw 0xa1ffbfbfef0f7bdb 0x743ff7f7fde1ef7b 0xffffffffff1fffff 0xffffffffffe3ffff

def z406 : W := mkw 0x00021210030e3101 0x200042420061c620 0xd8163630031e7305 0x7b02c6c60063ce60

def z407 : W := mkw 0x4372cfe597f29ea5 0xc86e59fcb2fe53d4 0xbfebcbcd9fe39ce3 0xf7fd7979b3fc739c

def z408 : W := mkw 0x00400c0a00000000 0x0008018140000000 0x00000c0e00000000 0xc0000181c0000000

def z409 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xd8163231e31e6005 0x3b02c6463c63cc00

def z410 : W := mkw 0x0002000002020001 0x0000400000404000 0x9802000003020001 0x3300400000604000

def z411 : W := mkw 0x048d300008096002 0x0091a60001012c00 0x0004300000006000 0x0000860000000c00

def z412 : W := mkw 0x2000001020040108 0x2400000204008021 0x0000043260000318 0x000000864c000063

def z413 : W := mkw 0x05bd300018996006 0x00b7a60003132c00 0xf5fff0001c1c6004 0x3ebffe0003838c00

def z414 : W := mkw 0x80cc0c0a08014052 0x101981814100280a 0x71cc0c0e0003e0f8 0xee398181c0007c1f

def z415 : W := mkw 0x45bff0859adbe0a7 0x88b7fe10b35b7c14 0xfdfff00d9fffe0e7 0xbfbffe01b3fffc1c

def z416 : W := mkw 0x45bde0c518f1c426 0x88b7bc18a31e3884 0x27e9c9cc1ce18c62 0x04fd3939839c318c

def z417 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff80c1ffffce7 0xffbfff0183ffff9c

def z418 : W := mkw 0x05bd300018996006 0x00b7a60003132c00 0x71dc30001c1fe007 0x2e3b86000383fc00

def z419 : W := mkw 0x03708ff515b41f04 0x606e11fea2b683e0 0xfffbcffd9ffc1f07 0xffff79ffb3ff83e0

def z420 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x88163233e31e6098 0xb102c6467c63cc13

def z421 : W := mkw 0x248f7000aa4be08b 0x8491ee0015497c11 0x040ff003e003e098 0xa081fe007c007c13

def z422 : W := mkw 0x0000000000000000 0x0000000000000000 0xd010063000000000 0x5a0200c600000000

def z423 : W := mkw 0xc0ce4e4a8f63def3 0xd819c9c951ec7bde 0x79cc0c0e1fe3ffff 0xef398181c3fc7fff

def z424 : W := mkw 0x82cc0e5a1db55f56 0x705981cb43b6abea 0x79cc0c0e1fffffff 0xef398181c3ffffff

def z425 : W := mkw 0x84ce5c0a1edbea57 0xd099cb8143db7d4a 0x79cc0c0e1fffffff 0xef398181c3ffffff

def z426 : W := mkw 0x0000025001241500 0x2000004a002482a0 0xfa300ff003fc1f07 0x5f4601fe007f83e0

def z427 : W := mkw 0x22021250b7be3f8d 0x6440424a16f7c7f1 0xd8163633fffe7f9f 0xfb02c6c67fffcff3

def z428 : W := mkw 0x8000000004000a50 0x500000000080014a 0x0000000000001ff8 0x00000000000003ff

def z429 : W := mkw 0x20000210a1041188 0x2400004214208231 0xd0163633e0001398 0xfa02c6c67c000273

def z430 : W := mkw 0x4332c3f593f695a5 0xa866587eb27ed2b4 0xbe3bcbfd83ff9ce3 0xf7c7797fb07ff39c

def z431 : W := mkw 0xa0421e1aa70e3bd9 0x740843c354e1c77b 0xd8163e3fe31e7ffd 0xfb02c7c7fc63cfff

def z432 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xcdf7f0001ffc6004 0x19befe0003ff8c00

def z433 : W := mkw 0xa0ce1e1aaf0f7bdb 0x7419c3c355e1ef7b 0xd9d63633ff1e739d 0xfb3ac6c67fe3ce73

def z434 : W := mkw 0x00cc0c0a08014002 0x0019818141002800 0x71cc0c0e1c03e007 0xee398181c3807c00

def z435 : W := mkw 0x0000021001041100 0x2000004200208220 0x88100230031c0000 0x1102004600638000

def z436 : W := mkw 0x0130024011b01404 0x0026004802360280 0xfbf00bc01ffc1c07 0x5f7e017803ff8380

def z437 : W := mkw 0x03700f6015b01e04 0x406e01ec02b603c0 0xbbe00bc01fe01c03 0x577c017803fc0380

def z438 : W := mkw 0x40000240812014a0 0x0800004810240294 0x0000000000001ce0 0x000000000000039c

def z439 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff633ffffe007 0xffbffec67ffffc00

def z440 : W := mkw 0x01bf3000020a2001 0x0037e60000414400 0xfdfff000031e6005 0x3fbffe000063cc00

def z441 : W := mkw 0x4002c085824280a1 0x88005810b0485014 0x040bc00d800380e0 0xa0817801b000701c

def z442 : W := mkw 0x400082c5812014a0 0x08001058b0240294 0x020003c180000000 0x0040007830000000

def z443 : W := mkw 0x6372dff5b7febfad 0xec6e5bfeb6ffd7f5 0xffffffffffffffff 0xffffffffffffffff

def z444 : W := mkw 0x25bf7210bbdff18f 0xa4b7ee42177bfe31 0xfdfff0001ffff39f 0x3fbffe0003fffe73

def z445 : W := mkw 0x01fdadaf48014002 0x003fb5b5e9002800 0xf7fffffffc03e007 0xfeffffffff807c00

def z446 : W := mkw 0x02408fff45241f00 0x604811ffe8a483e0 0x02000fffe0001f00 0xc04001fffc0003e0

def z447 : W := mkw 0x40024000824280a1 0x8800480010485014 0x00000000000380e0 0x000000000000701c

def z448 : W := mkw 0x05bff0851adbe007 0x80b7fe10a35b7c00 0xfffffbcd9fffe007 0xffffff79b3fffc00

def z449 : W := mkw 0x42408ff585241fa0 0x684811feb0a483f4 0x02000ffd80001fe0 0xc04001ffb00003fc

def z450 : W := mkw 0x41ffefefc36294a1 0x883ffdfdf86c5294 0xffffffffe3e00000 0xfffffffffc7c0000

def z451 : W := mkw 0x0330037011b41504 0x2066006e023682a0 0xba300bf003fc1c03 0x5746017e007f8380

def z452 : W := mkw 0x0000000010900004 0x0000000002120000 0x080000001ffc0007 0x0100000003ff8000

def z453 : W := mkw 0x20000210a1041188 0x2400004214208231 0x0000000000001398 0x0000000000000273

def z454 : W := mkw 0x40024240836294a1 0x88004848106c5294 0xbc2bc00003e39ce3 0x37857800007c739c

def z455 : W := mkw 0x81fd2d2a4c014a52 0x503fa5a54980294a 0x41d434327c00631c 0x083a86864f800c63

def z456 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0x060bcbcd80039ce0 0xe0c17979b000739c

def z457 : W := mkw 0x25bf7000badbe08f 0x84b7ee00175b7c11 0xfdfff003ffffe09f 0xbfbffe007ffffc13

def z458 : W := mkw 0x048f70000a4be003 0x8091ee0001497c00 0x75cff0001c03e007 0x2eb9fe0003807c00

def z459 : W := mkw 0x81fdadaf44000a50 0x503fb5b5e880014a 0xf7ffffffe0001ff8 0xfefffffffc0003ff

def z460 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xbe2bc3c183e38003 0x37c57878307c7000

def z461 : W := mkw 0x048d60000841c002 0x8091ac0001083800 0x0409c00000018000 0x0081380000003000

def z462 : W := mkw 0x0000000000000000 0x0000000000000000 0x5004000000026005 0x2a00800000004c00

def z463 : W := mkw 0x80cc0e4a0d215e52 0x501981c941a42bca 0xfbec0fce1fe3ffff 0xff7d81f9c3fc7fff

def z464 : W := mkw 0x83fdafff5db55f56 0x707fb5ffebb6abea 0xffffffffffffffff 0xffffffffffffffff

def z465 : W := mkw 0x03721f7017be3f05 0x606e43ee02f7c7e0 0xfbf63ff01ffe7f07 0x7f7ec7fe03ffcfe0

def z466 : W := mkw 0x03700d2014900a04 0x406e01a402920140 0x01c000001c000000 0x0038000003800000

def z467 : W := mkw 0x01bf600002428001 0x8037ec0000485000 0xfdfff00003e38003 0x3fbffe00007c7000

def z468 : W := mkw 0x0000021001041100 0x2000004200208220 0x0000063000001300 0x400000c600000260

def z469 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x71c40c021c007f1f 0x4e38818043800fe3

def z470 : W := mkw 0x80400c0a04000a50 0x500801814080014a 0x50040c0e00027ffd 0xea008181c0004fff

def z471 : W := mkw 0x05bf60001ad3c007 0x80b7ec00035a7800 0xbdebc0001fe38003 0x37bd780003fc7000

def z472 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x98123231e31e1081 0xf30246463c63c210

def z473 : W := mkw 0x0330013010940104 0x2066002602128020 0x00100030001c0000 0x0002000600038000

def z474 : W := mkw 0x400282c5832214a1 0x08005058b0644294 0x9a020bcd83021ce1 0xf3404179b060439c

def z475 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0x0c0bc00d83e39ce3 0xa1817801b07c739c

def z476 : W := mkw 0x05bf70000a4be003 0x80b7ee0001497c00 0xf5fff0000003e000 0x3ebffe0000007c00

def z477 : W := mkw 0x83fc0d3a1c954b56 0x707f81a74392a96a 0x71dc0c3e1c1fffff 0xee3b8187c383ffff

def z478 : W := mkw 0x01ffedaf42428001 0x803ffdb5e8485000 0xffffffffe3e38003 0xfffffffffc7c7000

def z479 : W := mkw 0x21721f30a30e3189 0x242e43e61461c631 0xfbf63ff3e31e739d 0xff7ec7fe7c63ce73

def z480 : W := mkw 0xa0021210af0f7bdb 0x7400424215e1ef7b 0xd8163633ff1fffff 0xfb02c6c67fe3ffff

def z481 : W := mkw 0x01fd2c0a00000000 0x003fa58140000000 0xf5fffc0e00000000 0xfebfff81c0000000

def z482 : W := mkw 0x20000210a1041188 0x2400004214208231 0x50040633e002739d 0xea0080c67c004e73

def z483 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x31c8080c1c039ce3 0xe63901018380739c

def z484 : W := mkw 0x00400d2000000000 0x000801a400000000 0x02000ff000000000 0x404001fe00000000

def z485 : W := mkw 0x00021000020a2001 0x0000420000414400 0x0006300000026000 0x2000c60000004c00

def z486 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0x8e2bc3cd83e380e0 0xb1c57879b07c701c

def z487 : W := mkw 0x23700f70b5b41f8c 0x646e01ee16b683f1 0xfbf00ff3fffc1f9f 0xdf7e01fe7fff83f3

def z488 : W := mkw 0x05bf72009bdbf087 0x80b7ee40137b7e10 0xfdfff2019ffff087 0xffbffe4033fffe10

def z489 : W := mkw 0x07fd3d301c9d6b06 0x60ffa7a60393ad60 0x41d434301c1c6304 0x083a868603838c60

def z490 : W := mkw 0x0000808500000000 0x00001010a0000000 0x040bc00d80000000 0xa0817801b0000000

def z491 : W := mkw 0x0000000008014002 0x0000000001002800 0x000000001c03e007 0x0000000003807c00

def z492 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0x0621c1c000000000 0x00c4383800000000

def z493 : W := mkw 0x0002400002428001 0x8000480000485000 0xbc2bc80c03e39ce3 0xf7857901807c739c

def z494 : W := mkw 0x0000000000000000 0x0000000000000000 0x1000000000021081 0xe200000000004210

def z495 : W := mkw 0x408ec2c58b63d4a3 0x8811d858b16c7a94 0xffefcbcd9fe3fce7 0xfffdf979b3fc7f9c

def z496 : W := mkw 0x27ff7f70bfffff8f 0xe4ffefee17fffff1 0xfffffff3ffffff9f 0xfffffffe7ffffff3

def z497 : W := mkw 0x0002420083429081 0x8000484010685210 0xbc2bc20183e39083 0xf7857840307c7210

def z498 : W := mkw 0x05bd700018d9e006 0x80b7ae00031b3c00 0x65fdf0001cfde006 0x0cbfbe00039fbc00

def z499 : W := mkw 0x0002020083021081 0x0000404010604210 0x0800000003021081 0x0100000000604210

def z500 : W := mkw 0x81fc0d2a0c014a52 0x503f81a54180294a 0xf3fc0ffe1c03ffff 0xfe7f81ffc3807fff

def z501 : W := mkw 0x07ffffff5fffff07 0xe0ffffffebffffe0 0xffffffffffffff07 0xffffffffffffffe0

def z502 : W := mkw 0x008c000008014002 0x0011800001002800 0x000c00000003e000 0x2001800000007c00

def z503 : W := mkw 0x03700d6014b00e04 0x406e01ac029601c0 0x73e00dc01ce01f07 0x4e7c01b8039c03e0

def z504 : W := mkw 0x0000000000000000 0x0000000000000000 0x3008080c00000000 0xe601010180000000

def z505 : W := mkw 0x07ff7d301edfeb07 0xe0ffefa603dbfd60 0xfdfff4301fffe307 0x3fbffe8603fffc60

def z506 : W := mkw 0x80ce4c0a0e43ca53 0xd019c98141c8794a 0xfdefcc0e1fe3ffff 0xffbdf981c3fc7fff

def z507 : W := mkw 0x00cc0c0a00000000 0x0019818140000000 0x71cc0c0e00039ce3 0xee398181c000739c

def z508 : W := mkw 0x03700d3014940b04 0x606e01a602928160 0xf9f004301ffc0307 0x1f3e008603ff8060

def z509 : W := mkw 0x0533700012daa005 0x80a66e00025b5400 0xdc37f00003fe6005 0x3b86fe00007fcc00

def z510 : W := mkw 0x0000000000000000 0x0000000000000000 0x00063003e0000000 0xa000c6007c000000

def z511 : W := mkw 0x0000808500000000 0x00001010a0000000 0x02000bcd80000000 0xc0400179b0000000

def z512 : W := mkw 0x20029295a30e3189 0x24005252b461c631 0xfe3fffffe31e739d 0xffc7fffffc63ce73

def z513 : W := mkw 0x41ffedafc24280a1 0x883ffdb5f8485014 0xf7ffffffe00380e0 0xfefffffffc00701c

def z514 : W := mkw 0x01fc0d2a00000000 0x003f81a540000000 0xf3fc0ffe00000000 0xfe7f81ffc0000000

def z515 : W := mkw 0x20000210a1041188 0x2400004214208231 0x00000231e0000000 0x000000463c000000

def z516 : W := mkw 0x848f700a0a4be053 0x9091ee0141497c0a 0x040ff00e0003e0f8 0xa081fe01c0007c1f

def z517 : W := mkw 0x23721f70b7be3f8d 0x646e43ee16f7c7f1 0xfbf23ff1fffc1f07 0x5f7e47fe3fff83e0

def z518 : W := mkw 0x8000000008014052 0x100000000100280a 0x000000000003e0f8 0x0000000000007c1f

def z519 : W := mkw 0x400082c5812014a0 0x08001058b0240294 0xb62bcbcd80001ce0 0xf6c57979b000039c

def z520 : W := mkw 0x0371aff555b41f04 0x606e35feaab683e0 0xfff3fff1fffc1f07 0x5ffe7ffe3fff83e0

def z521 : W := mkw 0x01708daf40000000 0x002e11b5e8000000 0xf3f00fffe0000000 0xde7e01fffc000000

def z522 : W := mkw 0x0000400000408000 0x8000080000081000 0x2429c00000e18002 0x04853800001c3000

def z523 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7fffffffc00631c 0xfeffffffff800c63

def z524 : W := mkw 0x800000000c014a52 0x500000000180294a 0x000000001c018c62 0x000000000380318c

def z525 : W := mkw 0xa0cc1c1a2c0d6b5a 0x741983834581ad6b 0x41d434327c1c631c 0x083a86864f838c63

def z526 : W := mkw 0x4002c085824280a1 0x88005810b0485014 0xb62bcbcd800380e0 0xf6c57979b000701c

def z527 : W := mkw 0x0131200000000000 0x0026240000000000 0x8433f00000000000 0x10867e0000000000

def z528 : W := mkw 0x07725f701fffff07 0xe0ee4bee03ffffe0 0xfbf00ff01fffff07 0x5f7e01fe03ffffe0

def z529 : W := mkw 0x81fd2c0a0c014a52 0x503fa5814180294a 0xf5fffc0e1c03ffff 0xfebfff81c3807fff

def z530 : W := mkw 0x21ffbfbfe30e3189 0x243ff7f7fc61c631 0xffffffffe31c0000 0xfffffffffc638000

def z531 : W := mkw 0x02400f7005241f00 0x604801ee00a483e0 0xba200ff003e01f03 0x574401fe007c03e0

def z532 : W := mkw 0x43708ff595b41fa4 0x686e11feb2b683f4 0xfbf00ffd9ffc1fe7 0xdf7e01ffb3ff83fc

def z533 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0x67fdfdfe60000000 0x0cffbfbfcc000000

def z534 : W := mkw 0x0200025015b41f04 0x6040004a02b683e0 0xd81006301ffc1f07 0x5b0200c603ff83e0

def z535 : W := mkw 0x20001010200c2108 0x2400020204018421 0x00000000001c631c 0x0000000000038c63

def z536 : W := mkw 0x23701f7035bc3f0c 0x646e03ee06b787e1 0xfbf43ff27ffc7f1f 0x5f7e87fe4fff8fe3

def z537 : W := mkw 0x00cc0c0a04000a00 0x4019818140800140 0x71cc0c0e1c001f07 0xee398181c38003e0

def z538 : W := mkw 0x4133e3e5c36294a1 0x88267c7cb86c5294 0x8e33f3f1e3e00000 0x11c67e7e3c7c0000

def z539 : W := mkw 0x20429fbfe30e3189 0x240853f7fc61c631 0xda163fffe31e739d 0xfb42c7fffc63ce73

def z540 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000039ce3 0x000000000000739c

def z541 : W := mkw 0x053370001adbe007 0x80a66e00035b7c00 0x8c33f0001fffe007 0x11867e0003fffc00

def z542 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0x8e23c3c183e39ce3 0x11c47878307c739c

def z543 : W := mkw 0x2000100020082008 0x0400020004010401 0x0004300260006018 0x000086004c000c03

def z544 : W := mkw 0x01fd2d2000000000 0x003fa5a400000000 0xf7fffff000000000 0x7efffffe00000000

def z545 : W := mkw 0x02400d3004040b00 0x604801a600808160 0x0000043000000300 0x0000008600000060

def z546 : W := mkw 0x01bd200008014002 0x0037a40001002800 0xf5fff0001c03e007 0x3ebffe0003807c00

def z547 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0x9e23c3c183e21081 0xf3c47878307c4210

def z548 : W := mkw 0x80400c0a04000a50 0x500801814080014a 0x30080c0e00039ffb 0xe6010181c00073ff

def z549 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x71cc0c0e1c00631c 0xee398181c3800c63

def z550 : W := mkw 0x448ff2c58b6bf4a3 0x8891fe58b16d7e94 0xbe2ffbcd83e3fce3 0xf7c5ff79b07c7f9c

def z551 : W := mkw 0x0330037011b41504 0x2066006e023682a0 0xda3007f003fc1305 0x5b4600fe007f8260

def z552 : W := mkw 0x4370cde514f08e24 0xc86e19bca29e11c4 0x27e9c9cc1ce18c62 0x04fd3939839c318c

def z553 : W := mkw 0x03720f7097b61f85 0x606e41ee12f6c3f0 0xfbf20ff19ffe1f87 0xff7e41fe33ffc3f0

def z554 : W := mkw 0x0130000000000000 0x0026000000000000 0xf1f0000000000000 0x1e3e000000000000

def z555 : W := mkw 0x00408daf40000000 0x000811b5e8000000 0x020009cc00000000 0x0040013980000000

def z556 : W := mkw 0x80400c0a04000a50 0x500801814080014a 0x71c00c0e1c001fff 0xce380181c38003ff

def z557 : W := mkw 0x07fd6f701df5df06 0xe0ffadee03bebbe0 0xfff9cff01ffd9f07 0x5fff39fe03ffb3e0

def z558 : W := mkw 0x808c000a0c014a52 0x501180014180294a 0x000c000e1c03ffff 0xa0018001c3807fff

def z559 : W := mkw 0x0733737013feb505 0xa0e66e6e027fd6a0 0x8e33f3f003fc0000 0x11c67e7e007f8000

def z560 : W := mkw 0xc3fecfff9ff7dff7 0xf87fd9fff3fefbfe 0xffffcfff9fffffff 0xfffff9fff3ffffff

def z561 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xd8123631e31c1305 0x5b0246c63c638260

def z562 : W := mkw 0x20021000a20a2089 0x0400420014414411 0x50063403e002739d 0xea00c6807c004e73

def z563 : W := mkw 0x01ffbdaf420a2001 0x003ff7b5e8414400 0xffffffffe31e6005 0xfffffffffc63cc00

def z564 : W := mkw 0x40024240836294a1 0x88004848106c5294 0x3808080c03e39ce3 0xe7010101807c739c

def z565 : W := mkw 0x4242cff587669fa1 0xe84859feb0ecd3f4 0xbe2bcffd83e39fe3 0xf7c579ffb07c73fc

def z566 : W := mkw 0x4000c08500408020 0x88001810a0081004 0x0409c00c00018060 0x008138018000300c

def z567 : W := mkw 0x01bda08500000000 0x0037b410a0000000 0xf7fffbcd80000000 0xfeffff79b0000000

def z568 : W := mkw 0xa08e100aaa0b60db 0x1411c20155416c1b 0x000e300fe003e0f8 0xa001c601fc007c1f

def z569 : W := mkw 0x008da08f40000000 0x0011b411e8000000 0xb62ffbcfe0000000 0xf6c5ff79fc000000

def z570 : W := mkw 0x80cc8c8f0c014a52 0x50199191e180294a 0xf7efcfcf9c03ffff 0xfefdf9f9f3807fff

def z571 : W := mkw 0x05bf30001a9b6007 0x00b7e60003536c00 0xd9d630001f1e6005 0x3b3ac60003e3cc00

def z572 : W := mkw 0x25337210b3deb18d 0xa4a66e42167bd631 0xdc37f633e3fe739d 0xfb86fec67c7fce73

def z573 : W := mkw 0xc002c2c58f63def3 0xd8005858b1ec7bde 0xbe2bcbcd9fe3ffff 0xf7c57979b3fc7fff

def z574 : W := mkw 0xc08ec2cf8b63d4f3 0x9811d859f16c7a9e 0xbe2fcbcf83e3fcfb 0xf7c5f979f07c7f9f

def z575 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x88123633e31c1398 0xd10246c67c638273

def z576 : W := mkw 0x80400c000c014a52 0x500801800180294a 0x71c00c001c03ffff 0x4e38018003807fff

def z577 : W := mkw 0x0000000004000a00 0x4000000000800140 0x000000001c001f07 0x00000000038003e0

def z578 : W := mkw 0x800000000c014a52 0x500000000180294a 0x500404021c03ffff 0xea00808043807fff

def z579 : W := mkw 0x448ff0858a4be0a3 0x8891fe10b1497c14 0x040ff00d8003e0e0 0xa081fe01b0007c1c

def z580 : W := mkw 0x400082c5812014a0 0x08001058b0240294 0x32080bcd80039ce3 0xe6410179b000739c

def z581 : W := mkw 0x20421e10a70e3b89 0x640843c214e1c771 0xf9d63e33ff1e7f9f 0xff3ac7c67fe3cff3

def z582 : W := mkw 0x00cc0c0a00000000 0x0019818140000000 0xf1de3e3fe0000000 0xfe3bc7c7fc000000

def z583 : W := mkw 0x0000021001041100 0x2000004200208220 0xd8163633e31c1305 0xfb02c6c67c638260

def z584 : W := mkw 0x05bff08f5adbe007 0x80b7fe11eb5b7c00 0xfdfff00fffffe007 0xbfbffe01fffffc00

def z585 : W := mkw 0x040250001adbe007 0x80804a00035b7c00 0xd81630001fffe007 0x3b02c60003fffc00

def z586 : W := mkw 0x40024240836294a1 0x88004848106c5294 0x0800000003e00000 0x01000000007c0000

def z587 : W := mkw 0x208e1210ab0f718b 0x2411c2421561ee31 0xf9de3633ff1ff39f 0xff3bc6c67fe3fe73

def z588 : W := mkw 0x07bf72501fffff07 0xe0f7ee4a03ffffe0 0xfdfff0001fffff07 0x3fbffe0003ffffe0

def z589 : W := mkw 0x4202c2d597f69fa5 0xe840585ab2fed3f4 0xbe2bcbcd9fff9fe7 0xf7c57979b3fff3fc

def z590 : W := mkw 0x0000000000000000 0x0000000000000000 0x00000633e0000000 0xc00000c67c000000

def z591 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0x77edcdce00000000 0xeefdb9b9c0000000

def z592 : W := mkw 0x000082c501201400 0x00001058a0240280 0xbe2bcbcd83e01c03 0xf7c57979b07c0380

def z593 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x71cc04021c03e31f 0x2e39808043807c63

def z594 : W := mkw 0x03fdafff45241f00 0x607fb5ffe8a483e0 0xf7ffffffe0001f00 0xfefffffffc0003e0

def z595 : W := mkw 0x41ffefefc36294a1 0x883ffdfdf86c5294 0xbfebcbcd83e39ce3 0xf7fd7979b07c739c

def z596 : W := mkw 0x22400f70a5241f88 0x644801ee14a483f1 0x02000ff3e0001f98 0xc04001fe7c0003f3

def z597 : W := mkw 0x008da08f40000000 0x0011b411e8000000 0xd41ff63fe0000000 0xfa83fec7fc000000

def z598 : W := mkw 0x00025000024aa001 0x80004a0000495400 0xfc3ff00003ffe007 0x3f87fe00007ffc00

def z599 : W := mkw 0x20001010200c2108 0x2400020204018421 0x50143432601e739d 0xea0286864c03ce73

def z600 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x71c80c0c1c019f67 0x4e390181838033ec

def z601 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x48143432631e739d 0x090286864c63ce73

def z602 : W := mkw 0x05bd600018d1c006 0x80b7ac00031a3800 0x75edc0001ce3e007 0x2ebdb800039c7c00

def z603 : W := mkw 0x01700d2000000000 0x002e01a400000000 0x23e009c000000000 0x047c013800000000

def z604 : W := mkw 0x21321210b39e318d 0x242642421673c631 0xf9f63633fffe739f 0xff3ec6c67fffce73

def z605 : W := mkw 0x25bd3010389d610e 0x24b7a6020713ac21 0x41d434327c1c631c 0x083a86864f838c63

def z606 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x08000633e31e739d 0xc10000c67c63ce73

def z607 : W := mkw 0x4402d2c59bfbf4a7 0x88805a58b37f7e94 0xbe2bcbcd9ffffce7 0xf7c57979b3ffff9c

def z608 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x000c0c0e0003fff8 0xe0018181c0007fff

def z609 : W := mkw 0x23701d30349c2b0c 0x646e03a606938561 0x41d434327c1c631c 0x083a86864f838c63

def z610 : W := mkw 0x02400f7005241f00 0x604801ee00a483e0 0xda100ff0031c1f05 0x5b4201fe006383e0

def z611 : W := mkw 0x0531300010982004 0x00a6260002130400 0x00103000001c0000 0x0002060000038000

def z612 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xabf00bf01ffc0c02 0x157e017e03ff8180

def z613 : W := mkw 0x03fdafff55b41f04 0x607fb5ffeab683e0 0xfff9cffc1ffc1f07 0x5fff39ff83ff83e0

def z614 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7fff9cc00000000 0x3effff3980000000

def z615 : W := mkw 0xc00242408f63def3 0xd800484811ec7bde 0x080000001fe3ffff 0x0100000003fc7fff

def z616 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xde37f7f3e3fe739d 0xfbc6fefe7c7fce73

def z617 : W := mkw 0x0400100018996006 0x0080020003132c00 0x000000001c1c6004 0x0000000003838c00

def z618 : W := mkw 0x0000024001201400 0x0000004800240280 0x02000bc000001c00 0x4040017800000380

def z619 : W := mkw 0xa0ce1c0aae0b6adb 0x5419c38155c16d5b 0x71ce3c0ffc03ffff 0xee39c781ff807fff

def z620 : W := mkw 0x840250001edbea57 0xd0804a0003db7d4a 0x080000001fffffff 0x0100000003ffffff

def z621 : W := mkw 0x20001010200c2108 0x2400020204018421 0x00103030601c0000 0x000206060c038000

def z622 : W := mkw 0x05bf72101bdff107 0xa0b7ee42037bfe20 0xfdfff6301ffff307 0x7fbffec603fffe60

def z623 : W := mkw 0x05bf72401bfbf407 0x80b7ee48037f7e80 0xfffffbc01ffffc07 0x7fffff7803ffff80

def z624 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0x8a300ff003fc1f00 0x514601fe007f83e0

def z625 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7ffffffe0039ce3 0xfefffffffc00739c

def z626 : W := mkw 0x83fc0f7a1db55f56 0x707f81ef43b6abea 0xfbf40ff21ffc7f1f 0x5f7e81fe43ff8fe3

def z627 : W := mkw 0x43724f7097f69fa5 0xe86e49ee12fed3f4 0xfbf00ff01fff9fe7 0x5f7e01fe03fff3fc

def z628 : W := mkw 0x00400c0000000000 0x0008018000000000 0x71c00c0000000000 0x4e38018000000000

def z629 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0x49d430001fffe007 0x093a860003fffc00

def z630 : W := mkw 0x800000000c014a52 0x500000000180294a 0x000000001c00631c 0x0000000003800c63

def z631 : W := mkw 0x8000000a00000050 0x100000014000000a 0x0000000e000000f8 0x80000001c000001f

def z632 : W := mkw 0x07737f7017febf05 0xe0ee6fee02ffd7e0 0xfff3fff01ffc1f07 0x5ffe7ffe03ff83e0

def z633 : W := mkw 0x01700d2000000000 0x002e01a400000000 0x41d0043000000000 0x083a008600000000

def z634 : W := mkw 0x03708fff55b41f04 0x606e11ffeab683e0 0xfbf00ffffffc1f07 0xdf7e01ffffff83e0

def z635 : W := mkw 0x03700f7011b41504 0x206e01ee023682a0 0xfbf00ff003fc0000 0x5f7e01fe007f8000

def z636 : W := mkw 0x0002400002428001 0x8000480000485000 0x8c23c00003e00000 0x11847800007c0000

def z637 : W := mkw 0x4533f2c593fab4a5 0x88a67e58b27f5694 0x8e33f3c183fc0000 0x11c67e78307f8000

def z638 : W := mkw 0x00400d2a40000000 0x000801a548000000 0x0000043260000000 0x000000864c000000

def z639 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x58040402031e739d 0xeb0080804063ce73

def z640 : W := mkw 0x24025210bbdff18f 0xa4804a42177bfe31 0x080000001ffff39f 0x0100000003fffe73

def z641 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000040200001398 0xc000008040000273

def z642 : W := mkw 0x85ff7c0a1edbea57 0xd0bfef8143db7d4a 0xfdfff80c1fffec67 0x3fbfff0183fffd8c

def z643 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xbe2bcbcd83e00000 0xf7c57979b07c0000

def z644 : W := mkw 0x04037000024aa001 0x80806e0000495400 0x0403f00000000000 0x00807e0000000000

def z645 : W := mkw 0x07ff7d601efbee07 0xc0ffefac03df7dc0 0xfffff9c01fffec07 0x3fffff3803fffd80

def z646 : W := mkw 0x21fdafbfe1041188 0x243fb5f7fc208231 0xf7ffffffe0001398 0xfefffffffc000273

def z647 : W := mkw 0x0002c08502428001 0x80005810a0485000 0xbe2bcbcd83e38003 0xf7c57979b07c7000

def z648 : W := mkw 0x808c000a08014052 0x101180014100280a 0x300c080e0003fcfb 0xe6018101c0007f9f

def z649 : W := mkw 0x23721f70b7be3f8d 0x646e43ee16f7c7f1 0xfbf00ff01ffe7f9f 0x5f7e01fe03ffcff3

def z650 : W := mkw 0x01bd200000000000 0x0037a40000000000 0xf5fff633e0000000 0xfebffec67c000000

def z651 : W := mkw 0x03fd2f7015b41f04 0x607fa5ee02b683e0 0xfffffff01ffc1f07 0x7ffffffe03ff83e0

def z652 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0x0a000bcd83e39ce3 0xc1400179b07c739c

def z653 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0x45dff0001c1fe004 0x28bbfe000383fc00

def z654 : W := mkw 0x00cc0c0a00000000 0x0019818140000000 0x41c4040200000000 0x0838808040000000

def z655 : W := mkw 0x053250001adbe007 0x80a64a00035b7c00 0xf9f000001fffe007 0x1f3e000003fffc00

def z656 : W := mkw 0x008c000a00000000 0x0011800140000000 0x000c000e00000000 0xa0018001c0000000

def z657 : W := mkw 0x81fc0c0a1c914a56 0x503f81814392294a 0xf9fc0c0e1fffffff 0xff3f8181c3ffffff

def z658 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0x25eff0001ce3e002 0x24bdfe00039c7c00

def z659 : W := mkw 0xe0cededfaf6ffffb 0xfc19dbdbf5edffff 0xffffffffffffffff 0xffffffffffffffff

def z660 : W := mkw 0x00cdac8f40000000 0x0019b591e8000000 0x75cffc0fe0000000 0xeeb9ff81fc000000

def z661 : W := mkw 0x0000808f40000000 0x00001011e8000000 0x0000000fe0000000 0x80000001fc000000

def z662 : W := mkw 0x00400c0004000a00 0x4008018000800140 0x71c80c0c1c039fe7 0xee390181838073fc

def z663 : W := mkw 0x03700d7014b40f04 0x606e01ae029681e0 0x63f00df01cfc0f06 0x0c7e01be039f81e0

def z664 : W := mkw 0x83fc0f7a1db55f56 0x707f81ef43b6abea 0xfbf80ffc1ffd9f67 0x5f7f01ff83ffb3ec

def z665 : W := mkw 0x008e40000a43c003 0x8011c80001487800 0xfdefc0001fe3e007 0x3fbdf80003fc7c00

def z666 : W := mkw 0x008c000008014002 0x0011800001002800 0x71cc04021c03f39f 0xee39808043807e73

def z667 : W := mkw 0x20020210a3061189 0x240040421460c231 0x98020633e3021399 0xf30040c67c604273

def z668 : W := mkw 0x4372cff597f69fa5 0xe86e59feb2fed3f4 0xfff3cff19ffc1f07 0x5ffe79fe33ff83e0

def z669 : W := mkw 0x040250000a4be003 0x80804a0001497c00 0x000000000003e000 0x0000000000007c00

def z670 : W := mkw 0x0533f1a552daa005 0x80a67e34aa5b5400 0x8e33f3f1e3fc0000 0x11c67e7e3c7f8000

def z671 : W := mkw 0x0330037015b41f04 0x6066006e02b683e0 0x8a3003f01ffc1f07 0x1146007e03ff83e0

def z672 : W := mkw 0x21ffbdafe20a2089 0x043ff7b5fc414411 0xf7ffffffe0026098 0xfefffffffc004c13

def z673 : W := mkw 0x00400c0004000a00 0x4008018000800140 0x41c004001c000304 0x0838008003800060

def z674 : W := mkw 0x0002020083021081 0x0000404010604210 0xb80a0a0d83039ce3 0xf7014141b060739c

def z675 : W := mkw 0x00021000020a2001 0x0000420000414400 0xd8163633e31e6005 0xfb02c6c67c63cc00

def z676 : W := mkw 0x0000000000000000 0x0000000000000000 0xb820000003e00003 0x17040000007c0000

def z677 : W := mkw 0x0000000000000000 0x0000000000000000 0x9002020180000000 0xf200404030000000

def z678 : W := mkw 0x808c000a08014052 0x101180014100280a 0x0008000c00018060 0x000100018000300c

def z679 : W := mkw 0x85ff7c0a1edbea57 0xd0bfef8143db7d4a 0xfdfff4021fffe31f 0x3fbffe8043fffc63

def z680 : W := mkw 0x01700f3001041100 0x202e01e600208220 0xfbf00ff0031c1305 0x5f7e01fe00638260

def z681 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0x43d43fffe0000000 0xc87a87fffc000000

def z682 : W := mkw 0xa0400e1aa5041bd8 0x740801c354a0837b 0x00000e3fe0001ff8 0xc00001c7fc0003ff

def z683 : W := mkw 0x05ff7d201adbe007 0x80bfefa4035b7c00 0xfffffff01fffe007 0x7ffffffe03fffc00

def z684 : W := mkw 0x0002020083021081 0x0000404010604210 0x8802020183000000 0x1100404030600000

def z685 : W := mkw 0x03700d6014b00e04 0x406e01ac029601c0 0xf3f00ff01ce00c02 0x5e7e01fe039c0180

def z686 : W := mkw 0x6002d295a34eb1a9 0xac005a52b469d635 0xdc1ff63fe31ff3fd 0xfb83fec7fc63fe7f

def z687 : W := mkw 0x00cc8daf40000000 0x001991b5e8000000 0x73cc0fffe0000000 0xee7981fffc000000

def z688 : W := mkw 0x408fe2cfc36294a1 0x8811fc59f86c5294 0xbe2ffbcfe3e39ce3 0xf7c5ff79fc7c739c

def z689 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x71cc080c1c03ec67 0x2e39810183807d8c

def z690 : W := mkw 0x07fd3f701dbd7f06 0x60ffa7ee03b7afe0 0xfbf43ff01ffc7f07 0x5f7e87fe03ff8fe0

def z691 : W := mkw 0x0130021011941104 0x2026004202328220 0xf9f006301ffc1307 0x5f3e00c603ff8260

def z692 : W := mkw 0x008d200000000000 0x0011a40000000000 0x040ff00000000000 0x2081fe0000000000

def z693 : W := mkw 0x03700f7005241f00 0x606e01ee00a483e0 0xf3f00ff000001f00 0x5e7e01fe000003e0

def z694 : W := mkw 0x80ce1c0a0e0b6a53 0x5019c38141c16d4a 0xf9de3c0e1f1fffff 0xff3bc781c3e3ffff

def z695 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0x49d004301ffc1f07 0x093a008603ff83e0

def z696 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7f9cffc00000000 0x5eff39ff80000000

def z697 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xbe23cbc183e01c03 0x57c47978307c0380

def z698 : W := mkw 0x01fd2d2a40000000 0x003fa5a548000000 0xf5fff43260000000 0x3ebffe864c000000

def z699 : W := mkw 0x84cf7c0a0e4bea53 0xd099ef8141c97d4a 0x75cffc0e1c03ffff 0xeeb9ff81c3807fff

def z700 : W := mkw 0x01321000129a2005 0x0026420002534400 0xf9f630001ffe6007 0x3f3ec60003ffcc00

def z701 : W := mkw 0x21fd3d3a600c2108 0x243fa7a74c018421 0x41d43432601c631c 0x083a86864c038c63

def z702 : W := mkw 0x400082c5812014a0 0x08001058b0240294 0xba200bcd83e01ce3 0xd7440179b07c039c

def z703 : W := mkw 0x03700d3014940b04 0x606e01a602928160 0x71d00c301c1c1f07 0x4e3a0186038383e0

def z704 : W := mkw 0x008e10000a0b6003 0x0011c20001416c00 0xf9de30001f1fe007 0x3f3bc60003e3fc00

def z705 : W := mkw 0x2133b3b5e30e3189 0x24267676bc61c631 0x8e33f3f1e31c0000 0x11c67e7e3c638000

def z706 : W := mkw 0x048f70000a4be003 0x8091ee0001497c00 0xdc1ff000031fe005 0x3b83fe000063fc00

def z707 : W := mkw 0x03712f7015b41f04 0x606e25ee02b683e0 0xfff3fff01ffc1f07 0x5ffe7ffe03ff83e0

def z708 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x71cc0e3ffc03ffff 0xee3981c7ff807fff

def z709 : W := mkw 0x0442ddaf5adbe007 0x80885bb5eb5b7c00 0x0a000fffffffe007 0xc14001fffffffc00

def z710 : W := mkw 0x0130004010b00404 0x0026000802160080 0xfbf009c01ffc0c07 0x1f7e013803ff8180

def z711 : W := mkw 0x81fdadaf5c914a56 0x503fb5b5eb92294a 0xffffffffffffffff 0xffffffffffffffff

def z712 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xfe2fcfcf83ffffff 0xffc5f9f9f07fffff

def z713 : W := mkw 0x43700f7095b41fa4 0x686e01ee12b683f4 0xfbf00ff01ffc1fe7 0x5f7e01fe03ff83fc

def z714 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0x7dedc0001fffe007 0x2fbdb80003fffc00

def z715 : W := mkw 0x25bd6210b9d5d18e 0xa4b7ac42173aba31 0x25e9c633fce1939a 0xc4bd38c67f9c3273

def z716 : W := mkw 0x23700f70b5b41f8c 0x646e01ee16b683f1 0xfbf00ff1fffc1f07 0x5f7e01fe3fff83e0

def z717 : W := mkw 0x01708da500000000 0x002e11b4a0000000 0xf7ffffffe0000000 0xfefffffffc000000

def z718 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7fffffffc03e3fc 0xfeffffffff807c7f

def z719 : W := mkw 0x6533f2d5b3feb5ad 0xaca67e5ab67fd6b5 0x8e33f3f1e3fc0000 0x11c67e7e3c7f8000

def z720 : W := mkw 0x02408ff545241f00 0x604811fea8a483e0 0x02000ff1e0001f00 0x404001fe3c0003e0

def z721 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0x8637f3f3e0000000 0xb0c6fe7e7c000000

def z722 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7ffffffe00380e0 0xfefffffffc00701c

def z723 : W := mkw 0x648ff085aa4be0ab 0x8c91fe10b5497c15 0x040ff00fe003e0f8 0xa081fe01fc007c1f

def z724 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0xa62bcbcd80e18c62 0x14c57979b01c318c

def z725 : W := mkw 0x83fdadef5cb14e56 0x507fb5bdeb9629ca 0x27e9c9cc1ce18c62 0x04fd3939839c318c

def z726 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xbe2bcbcd83e3ffff 0xf7c57979b07c7fff

def z727 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xa7fffbffe0000000 0xb4ffff7ffc000000

def z728 : W := mkw 0x03700d3014940b04 0x606e01a602928160 0xfbf00ff01ffc0307 0x5f7e01fe03ff8060

def z729 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0x762dcdce00e3ffff 0xeec5b9b9c01c7fff

def z730 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xadfbf0001fffe007 0x15bf7e0003fffc00

def z731 : W := mkw 0x02400e5015b41f04 0x604801ca02b683e0 0xfbe00fc01ffc1f07 0x5f7c01f803ff83e0

def z732 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xae2bcbcd83e38ce2 0xb5c57979b07c719c

def z733 : W := mkw 0x45bdb2c599b974a6 0x08b7b658b3372e94 0x43d43bcd9c1c7ce4 0xc87a8779b3838f9c

def z734 : W := mkw 0x0002c08502428001 0x80005810a0485000 0xbe2bcbcd83e39ce3 0xf7c57979b07c739c

def z735 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xc8163633e31e639c 0xb902c6c67c63cc73

def z736 : W := mkw 0x01fd2d2000000000 0x003fa5a400000000 0xf7fffff3e0000000 0xfefffffe7c000000

def z737 : W := mkw 0x6002d2c5a36ab4a9 0x8c005a58b46d5695 0xfe3ffbcfe3fffcff 0xffc7ff79fc7fff9f

def z738 : W := mkw 0x4002c0c5826284a1 0x88005818b04c5094 0x362bc9cd80e39ce3 0xe6c57939b01c739c

def z739 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xbe2fcbcf83e3fcfb 0xf7c5f979f07c7f9f

def z740 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xfe2bcfcd83e39fe7 0xffc579f9b07c73fc

def z741 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff4021fffe31f 0x3fbffe8043fffc63

def z742 : W := mkw 0x87fd3d3a1c9d6b56 0x70ffa7a74393ad6a 0x41d434321c1c631c 0x083a868643838c63

def z743 : W := mkw 0x01bda1a540000000 0x0037b434a8000000 0x863ff3f1e0000000 0x30c7fe7e3c000000

def z744 : W := mkw 0x20001210a10c3188 0x2400024214218631 0x50143633e01e739d 0xea0286c67c03ce73

def z745 : W := mkw 0x6000d0d5206ca528 0xac001a1aa40d94a5 0x663dfdfe60fdef7e 0x0cc7bfbfcc1fbdef

def z746 : W := mkw 0x01bda1af40000000 0x0037b435e8000000 0xf7fff3ffe0000000 0xbefffe7ffc000000

def z747 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfffffbc01fffe007 0x7fffff7803fffc00

def z748 : W := mkw 0x01bf3000129a2005 0x0037e60002534400 0xfdfff0001ffe6007 0x3fbffe0003ffcc00

def z749 : W := mkw 0x048ff0854a4be003 0x8091fe10a9497c00 0x040ff001e003e000 0x2081fe003c007c00

def z750 : W := mkw 0xc0cececf8f63def3 0xd819d9d9f1ec7bde 0xcfe7c7c39fe0631c 0x19fcf8f873fc0c63

def z751 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xfe3bcffd83e39ce3 0xffc779ffb07c739c

def z752 : W := mkw 0x4000c2c5816094a0 0x88001858b02c1294 0x2629cbcd80e18c62 0x04c53979b01c318c

def z753 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x21cc0c0e1c03fffa 0xe4398181c3807fff

def z754 : W := mkw 0x4002d2d5836eb5a1 0xa8005a5ab06dd6b4 0xfe3ffffd83ffffe7 0xffc7ffffb07ffffc

def z755 : W := mkw 0x4002c0c502628421 0x88005818a04c5084 0x262bc9cc00e38c62 0x24c57939801c718c

def z756 : W := mkw 0x60025250a36eb5a9 0xac004a4a146dd6b5 0xf81e3e3fe3ffffff 0xff03c7c7fc7fffff

def z757 : W := mkw 0x83bc037a19b55556 0x3077806f4336aaaa 0x8a3c03fe03ffe0f8 0xb147807fc07ffc1f

def z758 : W := mkw 0x6002c2d5a36695a9 0xac00585ab46cd2b5 0xfe2fcfffe3e3ffff 0xffc5f9fffc7c7fff

def z759 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x40163633e01e739c 0xe802c6c67c03ce73

def z760 : W := mkw 0x03fdadaf54900a04 0x407fb5b5ea920140 0xf7fffffffc000000 0xfeffffffff800000

def z761 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0x8633f7f3e0000000 0xd0c67efe7c000000

def z762 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0x8df3f0001ffc0000 0x11be7e0003ff8000

def z763 : W := mkw 0x01fdadaf50900004 0x003fb5b5ea120000 0xf7fffffffce00002 0xfeffffffff9c0000

def z764 : W := mkw 0x4002c2d5836695a1 0xa800585ab06cd2b4 0xfe3fcfff83ffffff 0xffc7f9fff07fffff

def z765 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0xf1ce0e0f9c03ffff 0xfe39c1c1f3807fff

def z766 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0xd637f7f3e002739d 0xfac6fefe7c004e73

def z767 : W := mkw 0x0330037011b41504 0x2066006e023682a0 0xfbf00bf01ffc1c07 0x5f7e017e03ff8380

def z768 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0xf63fffffe0000000 0xfec7fffffc000000

def z769 : W := mkw 0x60025250a36eb5a9 0xac004a4a146dd6b5 0xfa363ff3e3ffffff 0xff46c7fe7c7fffff

def z770 : W := mkw 0x01700d2010900004 0x002e01a402120000 0xfbf009c01ffc0007 0x1f7e013803ff8000

def z771 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7ffffffe000631c 0xfefffffffc000c63

def z772 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf80ffc1ffd9f67 0x5f7f01ff83ffb3ec

def z773 : W := mkw 0x20021250a32e3589 0x2400424a1465c6b1 0xd8163633e3fe7f9f 0xfb02c6c67c7fcff3

def z774 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7ffffffe0018c62 0xfefffffffc00318c

def z775 : W := mkw 0x8131a1a54c014a52 0x50263434a980294a 0x8633f3f1fc03ffff 0x10c67e7e3f807fff

def z776 : W := mkw 0x22408fffe5241f88 0x644811fffca483f1 0x02000fffe0001f98 0xc04001fffc0003f3

def z777 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xffffffffe3e00003 0xfffffffffc7c0000

def z778 : W := mkw 0x0330037011b41504 0x2066006e023682a0 0xfbf007f01ffc1307 0x5f7e00fe03ff8260

def z779 : W := mkw 0x01700d2014900a04 0x402e01a402920140 0xfbf00ff01ffc1f07 0x5f7e01fe03ff83e0

def z780 : W := mkw 0x6332d3f5b3feb5ad 0xac665a7eb67fd6b5 0x8e33f3f1e3fc0000 0x11c67e7e3c7f8000

def z781 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xadfff0001fffe002 0x35bffe0003fffc00

def z782 : W := mkw 0x0132500012daa005 0x80264a00025b5400 0xfdfff0001fffe007 0x3fbffe0003fffc00

def z783 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0x2629c9cc00e19ce2 0xc4c53939801c339c

def z784 : W := mkw 0x01bda1a540000000 0x0037b434a8000000 0xf7fffbfde0000000 0xfeffff7fbc000000

def z785 : W := mkw 0x4002c0c5826284a1 0x88005818b04c5094 0x2629c9cc00e38ce2 0x04c53939801c719c

def z786 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xd8163633e31c731d 0x5b02c6c67c638e63

def z787 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7fffffffc007ffc 0xfeffffffff800fff

def z788 : W := mkw 0x60025250a36eb5a9 0xac004a4a146dd6b5 0x0800000003fe739d 0x01000000007fce73

def z789 : W := mkw 0x008e50000a4be003 0x8011ca0001497c00 0xfdfff0001fffe007 0x3fbffe0003fffc00

def z790 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0x2be009c01ffc0c02 0x057c013803ff8180

def z791 : W := mkw 0x06cf7f700f6fff03 0xe0d9efee01edffe0 0x060ffff00003ff00 0x60c1fffe00007fe0

def z792 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7ffffffe003ffff 0xfefffffffc007fff

def z793 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7fffffffc02739d 0xfeffffffff804e73

def z794 : W := mkw 0x20001010200c2108 0x2400020204018421 0xc0163633e01c631c 0x1802c6c67c038c63

def z795 : W := mkw 0x80cdadaf4c014a52 0x5019b5b5e980294a 0x77cffffffc03ffff 0xeef9ffffff807fff

def z796 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xfe3bcffd83ffffff 0xffc779ffb07fffff

def z797 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0xb63bf3f1e0000000 0x36c77e7e3c000000

def z798 : W := mkw 0x4002c0c5826284a1 0x88005818b04c5094 0x262bc9cd80e18c62 0x04c57939b01c318c

def z799 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff4001ffff307 0x7fbffe8003fffe60

def z800 : W := mkw 0x82408fff45241f50 0x704811ffe8a483ea 0x02000fffe0001ff8 0xc04001fffc0003ff

def z801 : W := mkw 0x05bd600018d1c006 0x80b7ac00031a3800 0xfdfff0001ffd8007 0x3fbffe0003ffb000

def z802 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff633fffff39f 0xffbffec67ffffe73

def z803 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff4021fffe007 0xffbffe8043fffc00

def z804 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xfe2fcbcd83e3fce7 0xffc5f979b07c7f9c

def z805 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf63ff01ffc1f07 0x7f7ec7fe03ff83e0

def z806 : W := mkw 0x0330037011b41504 0x2066006e023682a0 0xcbf003f01ffc0004 0x197e007e03ff8000

def z807 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x71dc3c3e7c03ffff 0xee3b8787cf807fff

def z808 : W := mkw 0x048ff0850a4be003 0x8091fe10a1497c00 0x040ff00d8003e000 0xa081fe01b0007c00

def z809 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0x47dfffffe0000000 0xe8fbfffffc000000

def z810 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfffc0e1fffffff 0xffbfff81c3ffffff

def z811 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff0001ffc6004 0x3fbffe0003ff8c00

def z812 : W := mkw 0xe0025250af6ffffb 0xfc004a4a15edffff 0x080000001fffffff 0x0100000003ffffff

def z813 : W := mkw 0x21ffbfbfe30e3189 0x243ff7f7fc61c631 0x2fe9c9cc031e739d 0x05fd39398063ce73

def z814 : W := mkw 0x03700d6014b00e04 0x406e01ac029601c0 0xabf009c01ffc0c02 0x157e013803ff8180

def z815 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0x262bcbcd80e39ce2 0xe4c57979b01c739c

def z816 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xbe2bcbcd83e18c62 0xf7c57979b07c318c

def z817 : W := mkw 0x01be40001ad3c007 0x8037c800035a7800 0xfdffc0001fffe007 0x3fbff80003fffc00

def z818 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff6301fffe007 0x7fbffec603fffc00

def z819 : W := mkw 0x85bf700a1adbe057 0x90b7ee01435b7c0a 0xfdfff80e1ffffcff 0xffbfff01c3ffff9f

def z820 : W := mkw 0xc2408fff85241ff0 0x784811fff0a483fe 0x02000fff80001ff8 0xc04001fff00003ff

def z821 : W := mkw 0x0130025011b41504 0x2026004a023682a0 0xfbf00ff01ffc1f07 0x5f7e01fe03ff83e0

def z822 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x41c40c0e1c03ffff 0xc8388181c3807fff

def z823 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff80c1fffec67 0x3fbfff0183fffd8c

def z824 : W := mkw 0x62408ff5a5241fa8 0x6c4811feb4a483f5 0x02000fffe0001ff8 0xc04001fffc0003ff

def z825 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff003ffffe007 0xbfbffe007ffffc00

def z826 : W := mkw 0x0002424003629401 0x80004848006c5280 0xbe2bcbcc03e39ce3 0xf7c57979807c739c

def z827 : W := mkw 0x20025210a34eb189 0xa4004a421469d631 0xdc1ff633e31ff39d 0xfb83fec67c63fe73

def z828 : W := mkw 0x448ff08fca4be0a3 0x8891fe11f9497c14 0x040ff00fe003e0e0 0xa081fe01fc007c1c

def z829 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xc7fff7ffe0000000 0xb8fffefffc000000

def z830 : W := mkw 0x20021010a20e2189 0x240042021441c431 0xd0163633e01e639c 0xfa02c6c67c03cc73

def z831 : W := mkw 0x048e50001adbe007 0x8091ca00035b7c00 0xfdefc0001fffe007 0x3fbdf80003fffc00

def z832 : W := mkw 0x0130400010d08004 0x80260800021a1000 0xfdf9c0001ffd8007 0x1fbf380003ffb000

def z833 : W := mkw 0x01bda08500000000 0x0037b410a0000000 0xf7ffffffe0000000 0xfefffffffc000000

def z834 : W := mkw 0x0330037015b41f04 0x6066006e02b683e0 0xfbf003f01ffc1f07 0x1f7e007e03ff83e0

def z835 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf00ff01ffe7f9f 0x5f7e01fe03ffcff3

def z836 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x41cc0c0e1c03fffc 0xe8398181c3807fff

def z837 : W := mkw 0x02400f7015b41f04 0x604801ee02b683e0 0x7bc00ff01ffc1f07 0x4f7801fe03ff83e0

def z838 : W := mkw 0x0000808500000000 0x00001010a0000000 0xd637f7f3e0000000 0xfac6fefe7c000000

def z839 : W := mkw 0x01700f3011941104 0x202e01e602328220 0xfbf00ff01ffc1307 0x5f7e01fe03ff8260

def z840 : W := mkw 0x0171ada540000000 0x002e35b4a8000000 0xf7fbfffde0000000 0xfeff7fffbc000000

def z841 : W := mkw 0x01700e4015b01e04 0x402e01c802b603c0 0xfbf00fc01ffc1f07 0x5f7e01f803ff83e0

def z842 : W := mkw 0x81fdadaf44000a50 0x503fb5b5e880014a 0xf7ffffffe0000318 0xfefffffffc000063

def z843 : W := mkw 0x25bf7000badbe08f 0x84b7ee00175b7c11 0xfdfff633ffffe09f 0xffbffec67ffffc13

def z844 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0xa63bfbfde0000000 0x14c77f7fbc000000

def z845 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff231ffffe007 0x3fbffe463ffffc00

def z846 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0x2629c9cc00e39ce3 0x04c53939801c739c

def z847 : W := mkw 0x00cc8c8f00000000 0x00199191e0000000 0xf7ffffffe0000000 0xfefffffffc000000

def z848 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0xbe29c9cc03e18c63 0x17c53939807c318c

def z849 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7ffffffe0026098 0xfefffffffc004c13

def z850 : W := mkw 0x00400e5005241f00 0x600801ca00a483e0 0xfbf00ff01ffc1f07 0x5f7e01fe03ff83e0

def z851 : W := mkw 0x60025250a36eb5a9 0xac004a4a146dd6b5 0x0800000003ff9ce3 0x01000000007ff39c

def z852 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xc8163633e31e739d 0x1902c6c67c63ce73

def z853 : W := mkw 0x05bf700a1adbe007 0x80b7ee01435b7c00 0xfdfff00e1fffe007 0xbfbffe01c3fffc00

def z854 : W := mkw 0x60025250a36eb5a9 0xac004a4a146dd6b5 0xd8163633e3fe739d 0xfb02c6c67c7fce73

def z855 : W := mkw 0x0533700012daa005 0x80a66e00025b5400 0xfdf7f0001ffe6007 0x3fbefe0003ffcc00

def z856 : W := mkw 0x85fd3d2a5c996a56 0x50bfa7a54b932d4a 0x41d434327c1c631c 0x083a86864f838c63

def z857 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf00ff21ffc1f9f 0xdf7e01fe43ff83f3

def z858 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0xf1de3c0e1c03ffff 0xfe3bc781c3807fff

def z859 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf43ff27ffc1f07 0x5f7e87fe4fff83e0

def z860 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf63ff3fffe7f9f 0xff7ec7fe7fffcff3

def z861 : W := mkw 0x4372cdb596d68ba5 0xe86e59b6b2dad174 0x45dbc43d9c1f83e4 0xa8bb7887b383f07c

def z862 : W := mkw 0x20001010200c2108 0x2400020204018421 0x40163433e01c631c 0xa802c6867c038c63

def z863 : W := mkw 0x448ff0858a4be0a3 0x8891fe10b1497c14 0x040ff0018003e000 0x2081fe0030007c00

def z864 : W := mkw 0x01fdadaf58914006 0x003fb5b5eb122800 0xffffffffffffe007 0xfffffffffffffc00

def z865 : W := mkw 0x20025210a34eb189 0xa4004a421469d631 0xd8163633e3fff39f 0xfb02c6c67c7ffe73

def z866 : W := mkw 0x6002d2c5a36ab4a9 0x8c005a58b46d5695 0xbe2bfbcde3e39ce3 0xf7c57f79bc7c739c

def z867 : W := mkw 0x00cdadaf40000000 0x0019b5b5e8000000 0x77cfffffe0000000 0xeef9fffffc000000

def z868 : W := mkw 0x0171adaf40000000 0x002e35b5e8000000 0xd637ffffe0000000 0xfac6fffffc000000

def z869 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf20ff19ffc1f07 0xff7e41fe33ff83e0

def z870 : W := mkw 0x008c000008014002 0x0011800001002800 0x71cc0c0e1c03ffff 0xee398181c3807fff

def z871 : W := mkw 0x00400c0004000a00 0x4008018000800140 0x71cc0c0e1c03ffff 0xee398181c3807fff

def z872 : W := mkw 0x83fd2d3a5c954b56 0x707fa5a74b92a96a 0x41d434327c1c631c 0x083a86864f838c63

def z873 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7ffffffe0038003 0xfefffffffc007000

def z874 : W := mkw 0x4000c2c501609420 0x88001858a02c1284 0xbe29cbcc03e39ce3 0xf7c53979807c739c

def z875 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7fff7f3e0000000 0x3efffefe7c000000

def z876 : W := mkw 0x01bd200018914006 0x0037a40003122800 0xfdfff0001fffe007 0x3fbffe0003fffc00

def z877 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfbf0001ffd8007 0x1fbf7e0003ffb000

def z878 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xcbf00ff01ffc1f04 0x597e01fe03ff83e0

def z879 : W := mkw 0x05bd600018d1c006 0x80b7ac00031a3800 0x2de9c0001ffd8007 0x05bd380003ffb000

def z880 : W := mkw 0x60025250a36eb5a9 0xac004a4a146dd6b5 0x0800000003fc0000 0x01000000007f8000

def z881 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7fffffffc000007 0xfeffffffff800000

def z882 : W := mkw 0x20001210a10c3188 0x2400024214218631 0x40143633e01c631c 0x080286c67c038c63

def z883 : W := mkw 0x01fdadaf44000a00 0x403fb5b5e8800140 0xf7fffffffc000304 0xfeffffffff800060

def z884 : W := mkw 0x028da2df55b41f04 0x6051b45beab683e0 0x0c0ff00ffffc1f07 0xa181fe01ffff83e0

def z885 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7fffffffc000000 0xfeffffffff800000

def z886 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0x4ddff0001fffe007 0x29bbfe0003fffc00

def z887 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x61cc0c0e1c03ffff 0x0c398181c3807fff

def z888 : W := mkw 0x4002c2d5836695a1 0xa800585ab06cd2b4 0xbe2bcffd83e39fe3 0xf7c579ffb07c73fc

def z889 : W := mkw 0x03700d7014b40f04 0x606e01ae029681e0 0xfbf00df01ffc0f07 0x1f7e01be03ff81e0

def z890 : W := mkw 0x0171ada540000000 0x002e35b4a8000000 0xf7f7fff3e0000000 0xfefefffe7c000000

def z891 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xbe3bffffe3ff9ffb 0xf7c77ffffc7ff3ff

def z892 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbfc0ffe1fffffff 0xff7f81ffc3ffffff

def z893 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xdbf007f01ffc1305 0x5b7e00fe03ff8260

def z894 : W := mkw 0x01bda1af40000000 0x0037b435e8000000 0xb63ffbffe0000000 0xf6c7ff7ffc000000

def z895 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xfe3fffffe3ff9ce3 0xffc7fffffc7ff39c

def z896 : W := mkw 0x4000c2c501609420 0x88001858a02c1284 0xbe2bcbcd83e19c63 0xf7c57979b07c338c

def z897 : W := mkw 0x0000021001041100 0x2000004200208220 0xd8163633e31e739d 0xfb02c6c67c63ce73

def z898 : W := mkw 0x03700d6014b00e04 0x406e01ac029601c0 0x2be009c01ffc0c07 0x057c013803ff8180

def z899 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xbe2bcbcd83e38c63 0x37c57979b07c718c

def z900 : W := mkw 0x85737c0a16daaa55 0xd0ae6f8142db554a 0x8c33fc0e03fc1ff8 0xd1867f81c07f83ff

def z901 : W := mkw 0x00408daf40000000 0x000811b5e8000000 0xf63fffffe0000000 0xfec7fffffc000000

def z902 : W := mkw 0x60025210a34eb1a9 0xac004a421469d635 0xd8163633e31ff3fd 0xfb02c6c67c63fe7f

def z903 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xbe2ffbcfe3e39ce3 0xf7c5ff79fc7c739c

def z904 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xd81e363fe31ff3fd 0xfb03c6c7fc63fe7f

def z905 : W := mkw 0x4002d0c5026aa421 0x88005a18a04d5484 0xfe3ff9cc03ffec67 0x3fc7ff39807ffd8c

def z906 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xbe3bfbfde3e39ce3 0xf7c77f7fbc7c739c

def z907 : W := mkw 0x0130012010900004 0x0026002402120000 0xfbf003f01ffc0007 0x1f7e007e03ff8000

def z908 : W := mkw 0x01fdada540000000 0x003fb5b4a8000000 0xf7fffff1e0000000 0x7efffffe3c000000

def z909 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0x863fffffe0000000 0xf0c7fffffc000000

def z910 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xd7f7f7f3e0000000 0xfafefefe7c000000

def z911 : W := mkw 0x0000808500000000 0x00001010a0000000 0xf63fffffe003ffff 0xfec7fffffc007fff

def z912 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff0001ffd8002 0x3fbffe0003ffb000

def z913 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0xf9ec0c0e1fe3ffff 0xff3d8181c3fc7fff

def z914 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0xf1dc0e3e1c03ffff 0xfe3b81c7c3807fff

def z915 : W := mkw 0x848ff08f4a4be053 0x9091fe11e9497c0a 0x040ff00fe003e0f8 0xa081fe01fc007c1f

def z916 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf00ff3fffc1f07 0xdf7e01fe7fff83e0

def z917 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x48163433e31e739d 0xa902c6867c63ce73

def z918 : W := mkw 0x000082c501201400 0x00001058a0240280 0xbe2bcbcd83e39ce3 0xf7c57979b07c739c

def z919 : W := mkw 0x4000c2c5816094a0 0x88001858b02c1294 0xbe29cbcd83e19ce3 0xd7c53979b07c339c

def z920 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xfe3fffffe3e3ffff 0xffc7fffffc7c7fff

def z921 : W := mkw 0x0131a1a550900004 0x00263434aa120000 0xfff3f3f1fffc0007 0x1ffe7e7e3fff8000

def z922 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7ffffffe0001305 0xfefffffffc000260

def z923 : W := mkw 0x4002c0c502628421 0x88005818a04c5084 0xbe2bc9cc03e39ce3 0xf7c57939807c739c

def z924 : W := mkw 0x0000808500000000 0x00001010a0000000 0xb63bfbfde0000000 0xf6c77f7fbc000000

def z925 : W := mkw 0x4002c2d5836695a1 0xa800585ab06cd2b4 0xfe3fffffe3ff9fe7 0xffc7fffffc7ff3fc

def z926 : W := mkw 0x0130000010900004 0x0026000002120000 0xfbf00bc01ffc0007 0x5f7e017803ff8000

def z927 : W := mkw 0x85fdedaf5cd1ca56 0xd0bfbdb5eb9a394a 0x27e9c9cc1ce18c62 0x04fd3939839c318c

def z928 : W := mkw 0x4002d2c5836ab4a1 0x88005a58b06d5694 0xfe3fffffe3fffce7 0xffc7fffffc7fff9c

def z929 : W := mkw 0x048f70001adbe007 0x8091ee00035b7c00 0x7dcff0001fffe007 0x2fb9fe0003fffc00

def z930 : W := mkw 0x80cc0d2a4c014a52 0x501981a54980294a 0x71cc0c3e7c03ffff 0xee398187cf807fff

def z931 : W := mkw 0x20025210a34eb189 0xa4004a421469d631 0xdc37f633e3fe739d 0xfb86fec67c7fce73

def z932 : W := mkw 0x0000808500000000 0x00001010a0000000 0x8633f3f1e0000000 0x10c67e7e3c000000

def z933 : W := mkw 0x23721d60b6ba2e8d 0x446e43ac16d745d1 0x23e639c3fce26c9a 0xa47cc7387f9c4d93

def z934 : W := mkw 0xe0ce5e5aaf6ffffb 0xfc19cbcb55edffff 0x79cc0c0e1fffffff 0xef398181c3ffffff

def z935 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0x2e29c9cc03ffffff 0x05c53939807fffff

def z936 : W := mkw 0x4000c2c501609420 0x88001858a02c1284 0xae29cbcc03e18c62 0x15c53979807c318c

def z937 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7fffffffc007f1f 0xfeffffffff800fe3

def z938 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0x3629c9cc00e19c63 0x46c53939801c338c

def z939 : W := mkw 0x02408fff45241f00 0x604811ffe8a483e0 0x02000ffc00001f00 0x404001ff800003e0

def z940 : W := mkw 0x05bd600018d1c006 0x80b7ac00031a3800 0xadf9c0001ffd8002 0x15bf380003ffb000

def z941 : W := mkw 0x42408fffc5241fa0 0x684811fff8a483f4 0x02000fffe0001fe0 0xc04001fffc0003fc

def z942 : W := mkw 0x05bf60001ad3c007 0x80b7ec00035a7800 0xfdfbc0001fff8007 0x3fbf780003fff000

def z943 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0x87f3f3f1e0000000 0x10fe7e7e3c000000

def z944 : W := mkw 0x23700f70b5b41f8c 0x646e01ee16b683f1 0xfbf63ff3fffc1f9f 0xff7ec7fe7fff83f3

def z945 : W := mkw 0x0001a1a540000000 0x00003434a8000000 0x0603f3f1e0000000 0x00c07e7e3c000000

def z946 : W := mkw 0x4002d2c5836ab4a1 0x88005a58b06d5694 0xbe3bfbcd83ff9ce3 0xf7c77f79b07ff39c

def z947 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xfa363ff3e31e739d 0xff46c7fe7c63ce73

def z948 : W := mkw 0x6002c2c5a36294a9 0x8c005858b46c5295 0xbe2bcbcfe3e39cfb 0xf7c57979fc7c739f

def z949 : W := mkw 0x01fdadaf50900004 0x003fb5b5ea120000 0xffffffffe3fc0000 0xfffffffffc7f8000

def z950 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xbe2ffbcfe3ffffff 0xf7c5ff79fc7fffff

def z951 : W := mkw 0x20001010a00c2188 0x2400020214018431 0x40143433e01c639c 0x880286867c038c73

def z952 : W := mkw 0x4000c2d501649520 0xa800185aa02c92a4 0xfe39cffc03fd9f67 0x5fc739ff807fb3ec

def z953 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xbe3bfbfde3ffffff 0xf7c77f7fbc7fffff

def z954 : W := mkw 0x0171adaf40000000 0x002e35b5e8000000 0x8633fbfde0000000 0x10c67f7fbc000000

def z955 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf40ff21ffc7f1f 0x5f7e81fe43ff8fe3

def z956 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7fffffffc03e31f 0xfeffffffff807c63

def z957 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xbdebc0001fffe007 0x37bd780003fffc00

def z958 : W := mkw 0x448ff0850a4be023 0x8891fe10a1497c04 0x040ff00c0003e060 0x2081fe0180007c0c

def z959 : W := mkw 0x0330016010b00404 0x0066002c02160080 0xfbf001c01ffc0007 0x1f7e003803ff8000

def z960 : W := mkw 0x808c000a0c014a52 0x501180014180294a 0x71cc000e1c03ffff 0xae398001c3807fff

def z961 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xbe3ffbffe3fffcfb 0xf7c7ff7ffc7fff9f

def z962 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0x2e2bc9cd83e39ce3 0xa5c57939b07c739c

def z963 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xfe3bfffde3ff9fe7 0xffc77fffbc7ff3fc

def z964 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf00ff01fff9fe7 0x5f7e01fe03fff3fc

def z965 : W := mkw 0x0171adaf40000000 0x002e35b5e8000000 0xb63bffffe0000000 0xf6c77ffffc000000

def z966 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xffebcbcd9fe39ce7 0xfffd7979b3fc739c

def z967 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xd8163e3fe31e7ffd 0xfb02c7c7fc63cfff

def z968 : W := mkw 0x42408ff585241fa0 0x684811feb0a483f4 0x02000ff180001f00 0x404001fe300003e0

def z969 : W := mkw 0x85bf70001adbe057 0x90b7ee00035b7c0a 0xfdfff0001fffe0ff 0x3fbffe0003fffc1f

def z970 : W := mkw 0x6002c2d5a36695a9 0xac00585ab46cd2b5 0xfe3bcfffe3ff9fff 0xffc779fffc7ff3ff

def z971 : W := mkw 0x6002c2d5a36695a9 0xac00585ab46cd2b5 0xfe3fffffe3e39ffb 0xffc7fffffc7c73ff

def z972 : W := mkw 0xa5bf700abadbe0df 0x94b7ee01575b7c1b 0xfdfff00fffffe0ff 0xbfbffe01fffffc1f

def z973 : W := mkw 0x01700f6011b01404 0x002e01ec02360280 0xfbf00ff01ffc1c07 0x5f7e01fe03ff8380

def z974 : W := mkw 0x0171ada540000000 0x002e35b4a8000000 0xa7f3fbf1e0000000 0x14fe7f7e3c000000

def z975 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0x9633f3f1e0000000 0xf2c67e7e3c000000

def z976 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xddf7f0001ffe6005 0x3bbefe0003ffcc00

def z977 : W := mkw 0x0130000010900004 0x0026000002120000 0xfdfbc0001ffc0007 0x3fbf780003ff8000

def z978 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xb7fbfbfde0000000 0xf6ff7f7fbc000000

def z979 : W := mkw 0x4002c0c502628421 0x88005818a04c5084 0x2e29c9cc03e38c63 0x05c53939807c718c

def z980 : W := mkw 0x00021000020a2001 0x0000420000414400 0xd8163633e31e739d 0xfb02c6c67c63ce73

def z981 : W := mkw 0x01fdadaf50900004 0x003fb5b5ea120000 0xf7fffffffc1c0004 0xfeffffffff838000

def z982 : W := mkw 0x81fdadaf48014052 0x103fb5b5e900280a 0xf7ffffffe003fcfb 0xfefffffffc007f9f

def z983 : W := mkw 0x8171adaf44000a50 0x502e35b5e880014a 0x8633ffffe0001ff8 0xd0c67ffffc0003ff

def z984 : W := mkw 0x01fdadaf44000a00 0x403fb5b5e8800140 0xf7fffffffc039fe7 0xfeffffffff8073fc

def z985 : W := mkw 0x0130024011b01404 0x0026004802360280 0xfbf003c01ffc0007 0x1f7e007803ff8000

def z986 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0x2de9c0001ffd8002 0x05bd380003ffb000

def z987 : W := mkw 0x4002c0c502628421 0x88005818a04c5084 0xae2bc9cc03e18c62 0x15c57939807c318c

def z988 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x21cc080e1c03ffff 0xa4398101c3807fff

def z989 : W := mkw 0x03700f7011b41504 0x206e01ee023682a0 0xfbf00ff01ffc0007 0x5f7e01fe03ff8000

def z990 : W := mkw 0x01bda1a548014002 0x0037b434a9002800 0xf7fff3f1fc03e007 0x3efffe7e3f807c00

def z991 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0xb62bcbcd80e39ce3 0xf6c57979b01c739c

def z992 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0xc637f7f3e0000000 0x18c6fefe7c000000

def z993 : W := mkw 0x20001210210c3108 0x2400024204218621 0xd8163633e31c731d 0xfb02c6c67c638e63

def z994 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xcdf7f0001fffe007 0x19befe0003fffc00

def z995 : W := mkw 0x20021250a32e3589 0x2400424a1465c6b1 0xda163ff3e31e7f9d 0xfb42c7fe7c63cff3

def z996 : W := mkw 0x81fdadaf40000050 0x103fb5b5e800000a 0xf7ffffffe00000f8 0xfefffffffc00001f

def z997 : W := mkw 0x01bda1af40000000 0x0037b435e8000000 0xd63ff7ffe0000000 0xfac7fefffc000000

def z998 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xe7ffffffe0000000 0x1cfffffffc000000

def z999 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0x6dfdf0001fffe007 0x0dbfbe0003fffc00

def z1000 : W := mkw 0xe0408edfa5241ff8 0x7c0811dbf4a483ff 0x02000fffe0001ff8 0xc04001fffc0003ff

def z1001 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xd8163633e31e631d 0x3b02c6c67c63cc63

def z1002 : W := mkw 0x01fdadaf48014002 0x003fb5b5e9002800 0xf7ffffffe003e000 0xfefffffffc007c00

def z1003 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf80ff01fff9f07 0x7f7f01fe03fff3e0

def z1004 : W := mkw 0x05bf71201adbe007 0x80b7ee24035b7c00 0xfffff3f01fffe007 0x3ffffe7e03fffc00

def z1005 : W := mkw 0x01bda1a540000000 0x0037b434a8000000 0xc7f7f3f1e0000000 0x18fefe7e3c000000

def z1006 : W := mkw 0x01fdadaf48014002 0x003fb5b5e9002800 0xf7fffffffc006004 0xfeffffffff800c00

def z1007 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7ffffffe0021081 0xfefffffffc004210

def z1008 : W := mkw 0xa3700f7ab5b41fdc 0x746e01ef56b683fb 0xfbf00ffffffc1fff 0xdf7e01ffffff83ff

def z1009 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xae3bfbfde3fd8c62 0x15c77f7fbc7fb18c

def z1010 : W := mkw 0x03700d6014b00e04 0x406e01ac029601c0 0xfbf00dc01ffc1f07 0x5f7e01b803ff83e0

def z1011 : W := mkw 0x05fdadaf58914006 0x00bfb5b5eb122800 0xf7fffffffc000000 0xfeffffffff800000

def z1012 : W := mkw 0x20021010a20e2189 0x240042021441c431 0x50163433e01e739d 0xea02c6867c03ce73

def z1013 : W := mkw 0x01bda1a540000000 0x0037b434a8000000 0xf7fff7f3e0000000 0xfefffefe7c000000

def z1014 : W := mkw 0x008da08f40000000 0x0011b411e8000000 0xf63fffffe0000000 0xfec7fffffc000000

def z1015 : W := mkw 0x4000c2c501609420 0x88001858a02c1284 0x2629cbcc00e19c62 0x44c53979801c338c

def z1016 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xc8163633e31c739c 0xd902c6c67c638e73

def z1017 : W := mkw 0x0531600010d08004 0x80a62c00021a1000 0xfdf1c0001ffc0007 0x1fbe380003ff8000

def z1018 : W := mkw 0x25bf7000badbe08f 0x84b7ee00175b7c11 0xfdfff0001fffe09f 0x3fbffe0003fffc13

def z1019 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xa7fbfbfdfc018c62 0x14ff7f7fbf80318c

def z1020 : W := mkw 0x81fdadaf44000a50 0x503fb5b5e880014a 0xf7ffffffe0000c60 0xfefffffffc00018c

def z1021 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xbdfbf0001fff8003 0x37bf7e0003fff000

def z1022 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0xf63fffffe0e18c62 0xfec7fffffc1c318c

def z1023 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xfe3bcbcd83ff9ce7 0xffc77979b07ff39c

def z1024 : W := mkw 0x81fdadaf48014052 0x103fb5b5e900280a 0xf7ffffffe0018060 0xfefffffffc00300c

def z1025 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xfe3ffbcd83e39ce3 0xffc7ff79b07c739c

def z1026 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0x3e29c9cc03e39ce3 0xe7c53939807c739c

def z1027 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff8001ffffc07 0x7fbfff0003ffff80

def z1028 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf009c01ffc1f07 0x1f7e013803ff83e0

def z1029 : W := mkw 0x20021250a32e3589 0x2400424a1465c6b1 0xda3637f3e3fe739d 0xfb46c6fe7c7fce73

def z1030 : W := mkw 0x0131a1a550900004 0x00263434aa120000 0x8e33f3f1e3fc0000 0x11c67e7e3c7f8000

def z1031 : W := mkw 0x00cdadaf40000000 0x0019b5b5e8000000 0xb62fffffe0000000 0xf6c5fffffc000000

def z1032 : W := mkw 0x01fdadaf44000a00 0x403fb5b5e8800140 0xf7fffffffc027f9f 0xfeffffffff804ff3

def z1033 : W := mkw 0x6000c2d5a16495a8 0xac00185ab42c92b5 0x2629cfffe0e19ffa 0xc4c539fffc1c33ff

def z1034 : W := mkw 0xa0ce1e1aaf0f7bdb 0x7419c3c355e1ef7b 0xa9da3a3dff1d8c62 0x153b4747bfe3b18c

def z1035 : W := mkw 0x01fdadaf48014002 0x003fb5b5e9002800 0xf7fffffffc03fce7 0xfeffffffff807f9c

def z1036 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xfe3ffbfde3fffce7 0xffc7ff7fbc7fff9c

def z1037 : W := mkw 0x05bf71205adbe007 0x80b7ee240b5b7c00 0xfdfff0307fffe007 0x3fbffe060ffffc00

def z1038 : W := mkw 0x6002d2c5a36ab4a9 0x8c005a58b46d5695 0xfe2fffcfe3e3ffff 0xffc5fff9fc7c7fff

def z1039 : W := mkw 0x053250001adbe007 0x80a64a00035b7c00 0xfdfbc0001fffe007 0x3fbf780003fffc00

def z1040 : W := mkw 0x4000c2c5816094a0 0x88001858b02c1294 0x2629c9cc00e19ce2 0x04c53939801c339c

def z1041 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff0001ffff39f 0x3fbffe0003fffe73

def z1042 : W := mkw 0x03700f7095b41f84 0x606e01ee12b683f0 0xfbf00ff19ffc1f87 0xdf7e01fe33ff83f0

def z1043 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0x2629c9cc00e38ce2 0xa4c53939801c719c

def z1044 : W := mkw 0x048ff08f4a4be003 0x8091fe11e9497c00 0x040ff00c0003e000 0x2081fe0180007c00

def z1045 : W := mkw 0x4002d2c5836ab4a1 0x88005a58b06d5694 0xfe3fffcf83ffffff 0xffc7fff9f07fffff

def z1046 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf00ff01ffc0c02 0x5f7e01fe03ff8180

def z1047 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0x2e29cbcd83e39ce3 0xc5c53979b07c739c

def z1048 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xbbe00bc01ffc1f07 0x577c017803ff83e0

def z1049 : W := mkw 0x0533700012daa005 0x80a66e00025b5400 0xcdf3f0001ffc0004 0x19be7e0003ff8000

def z1050 : W := mkw 0x0132400012d28005 0x80264800025a5000 0xfdf3c0001ffc0007 0x1fbe780003ff8000

def z1051 : W := mkw 0x6002d2c5a36ab4a9 0x8c005a58b46d5695 0xfe3fffffe3e3fcfb 0xffc7fffffc7c7f9f

def z1052 : W := mkw 0x03700d6014b00e04 0x406e01ac029601c0 0xfbf00ff01ffc0c07 0x5f7e01fe03ff8180

def z1053 : W := mkw 0x01fdadaf48014002 0x003fb5b5e9002800 0xf7fffffffc03f39f 0xfeffffffff807e73

def z1054 : W := mkw 0x83700f7a15b41f54 0x706e01ef42b683ea 0xfbf40ffe1ffe7fff 0xff7e81ffc3ffcfff

def z1055 : W := mkw 0x05bd300018996006 0x00b7a60003132c00 0xfdfff0001ffc6007 0x3fbffe0003ff8c00

def z1056 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0x3629c9cc00e18c62 0xe6c53939801c318c

def z1057 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xae2bcbcd83e19ce2 0xd5c57979b07c339c

def z1058 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xebf00ff01ffc0f06 0x1d7e01fe03ff81e0

def z1059 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x71cc080c1c03ffff 0x2e39810183807fff

def z1060 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xf81e3e3fe31e739d 0xff03c7c7fc63ce73

def z1061 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7ffffffe0001398 0xfefffffffc000273

def z1062 : W := mkw 0x23700f70b5b41f8c 0x646e01ee16b683f1 0xfbf00ff01ffc1f9f 0x5f7e01fe03ff83f3

def z1063 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf00bf01ffc0c07 0x1f7e017e03ff8180

def z1064 : W := mkw 0x42408ff505241f20 0x684811fea0a483e4 0x02000ffc00001f60 0x404001ff800003ec

def z1065 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0x262bc9cd80e18c62 0xa4c57939b01c318c

def z1066 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xffffffffe31c0005 0xfffffffffc638000

def z1067 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0xf7f3f3f1e0000000 0x1efe7e7e3c000000

def z1068 : W := mkw 0x20001010200c2108 0x2400020204018421 0x40143633e01c631c 0xc80286c67c038c63

def z1069 : W := mkw 0x0131a1af40000000 0x00263435e8000000 0x8633f3ffe0000000 0x90c67e7ffc000000

def z1070 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7fffffffc03ecfa 0xfeffffffff807d9f

def z1071 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf007f01ffc0307 0x1f7e00fe03ff8060

def z1072 : W := mkw 0x0171ada544000a00 0x402e35b4a8800140 0xf7f3fff1fc001f07 0x5efe7ffe3f8003e0

def z1073 : W := mkw 0x20021010a20e2189 0x240042021441c431 0xd8163433e31e639d 0xbb02c6867c63cc73

def z1074 : W := mkw 0x0171ada540000000 0x002e35b4a8000000 0xc7f3f7f1e0000000 0x18fe7efe3c000000

def z1075 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7fffffffc01ef7e 0xfeffffffff803def

def z1076 : W := mkw 0x83700f7015b41f54 0x706e01ee02b683ea 0xfbf00ff01ffc1fff 0x5f7e01fe03ff83ff

def z1077 : W := mkw 0x20001210a10c3188 0x2400024214218631 0xd8143633e31c739d 0xdb0286c67c638e73

def z1078 : W := mkw 0x01bda1af40000000 0x0037b435e8000000 0x863bf3fde0000000 0x10c77e7fbc000000

def z1079 : W := mkw 0x4000c0c5806084a0 0x88001818b00c1094 0x2629c9cd80e18ce2 0x84c53939b01c319c

def z1080 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf00ffc1ffc1fe7 0xdf7e01ff83ff83fc

def z1081 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0x8bf003f01ffc0000 0x117e007e03ff8000

def z1082 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0xf5efcc0e1c03ffff 0xfebdf981c3807fff

def z1083 : W := mkw 0x60025250a36eb5a9 0xac004a4a146dd6b5 0xfc3ff633e3ffffff 0xff87fec67c7fffff

def z1084 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff4327fffe007 0x3fbffe864ffffc00

def z1085 : W := mkw 0x4002c0c5826284a1 0x88005818b04c5094 0xb62bcbcd80e38ce2 0xf6c57979b01c719c

def z1086 : W := mkw 0x0131200010900004 0x0026240002120000 0xfdf3f0001ffc0007 0x1fbe7e0003ff8000

def z1087 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0x8633fbfde0000000 0xd0c67f7fbc000000

def z1088 : W := mkw 0x60025250a36eb5a9 0xac004a4a146dd6b5 0x780c0c0e03ffffff 0xef018181c07fffff

def z1089 : W := mkw 0x85bf700a1adbe057 0x90b7ee01435b7c0a 0xfdfff0021fffe01f 0x3fbffe0043fffc03

def z1090 : W := mkw 0x01bda1a540000000 0x0037b434a8000000 0xa7fbf3f1e0000000 0x14ff7e7e3c000000

def z1091 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfffbcff01ffc1f07 0x7fff79fe03ff83e0

def z1092 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff80c1fffe007 0xffbfff0183fffc00

def z1093 : W := mkw 0x05bf700a5adbe007 0x80b7ee014b5b7c00 0xfdfff0027fffe007 0x3fbffe004ffffc00

def z1094 : W := mkw 0x81fdadaf48014052 0x103fb5b5e900280a 0xf7fffffffc03e0ff 0xfeffffffff807c1f

def z1095 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xbe2bc9cc03e39ce3 0x37c57939807c739c

def z1096 : W := mkw 0x62025250b7febfad 0xec404a4a16ffd7f5 0x080000001fffffff 0x0100000003ffffff

def z1097 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xd8163633e31fffff 0xfb02c6c67c63ffff

def z1098 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf00ff01ffe1f87 0xff7e01fe03ffc3f0

def z1099 : W := mkw 0x20001010200c2108 0x2400020204018421 0xd0163633e01e739d 0xfa02c6c67c03ce73

def z1100 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xbe2bcbcd83ff9ce3 0xf7c57979b07ff39c

def z1101 : W := mkw 0x6002d0c5a26aa4a9 0x8c005a18b44d5495 0x262ff9cfe0e3ecfa 0xa4c5ff39fc1c7d9f

def z1102 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7ffffffe0001ce0 0xfefffffffc00039c

def z1103 : W := mkw 0x80400c0a0c014a52 0x500801814180294a 0x71c00c0e1c03ffff 0xce380181c3807fff

def z1104 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x48143633e31e739d 0xc90286c67c63ce73

def z1105 : W := mkw 0x0533700012daa005 0x80a66e00025b5400 0xfdfbf0001fff8007 0x3fbf7e0003fff000

def z1106 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff0021fffe09f 0xbfbffe0043fffc13

def z1107 : W := mkw 0x01bda1af40000000 0x0037b435e8000000 0x8637f3f3e0000000 0x10c6fe7e7c000000

def z1108 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff0001ffffce7 0x3fbffe0003ffff9c

def z1109 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xf81e3633e31ff39f 0xff03c6c67c63fe73

def z1110 : W := mkw 0x01fdadaf54900a04 0x403fb5b5ea920140 0xfffffffffffc1f07 0xffffffffffff83e0

def z1111 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf80ffc1ffc1f07 0xff7f01ff83ff83e0

def z1112 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xbe2bcfffe3e39ce3 0xf7c579fffc7c739c

def z1113 : W := mkw 0x20025210a34eb189 0xa4004a421469d631 0xfc3ffe3fe3ffffff 0xff87ffc7fc7fffff

def z1114 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0xb633fbf1e0000000 0x56c67f7e3c000000

def z1115 : W := mkw 0x80cdadaf4c014a52 0x5019b5b5e980294a 0x060fffffe003fff8 0xe0c1fffffc007fff

def z1116 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x71c80c0c1c03ffff 0x4e39018183807fff

def z1117 : W := mkw 0x83700f7a15b41f54 0x706e01ef42b683ea 0xfbf00ff21ffc1f1f 0x5f7e01fe43ff83e3

def z1118 : W := mkw 0x85bf700a1adbe057 0x90b7ee01435b7c0a 0xfdfff00c1fffe067 0x3fbffe0183fffc0c

def z1119 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x21c80c0e1c03ffff 0xc4390181c3807fff

def z1120 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0x2629cbcd80e18c62 0xc4c53979b01c318c

def z1121 : W := mkw 0x01fdadaf44000a00 0x403fb5b5e8800140 0xf7fffffffc000c02 0xfeffffffff800180

def z1122 : W := mkw 0x41ff6f6ac36294a1 0x883feded586c5294 0x49d4343263e39ce3 0x093a86864c7c739c

def z1123 : W := mkw 0x0171ada540000000 0x002e35b4a8000000 0x8633fff1e0000000 0x50c67ffe3c000000

def z1124 : W := mkw 0x05bf700012daa005 0x80b7ee00025b5400 0xfdfff0001ffc0007 0x3fbffe0003ff8000

def z1125 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xfe3ffbcd83ffffff 0xffc7ff79b07fffff

def z1126 : W := mkw 0x00cdadaf40000000 0x0019b5b5e8000000 0xd61fffffe0000000 0xfac3fffffc000000

def z1127 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff2019fffe007 0xffbffe4033fffc00

def z1128 : W := mkw 0x80cc8c8f0c014a52 0x50199191e180294a 0xf7fffffffc03ffff 0xfeffffffff807fff

def z1129 : W := mkw 0x81fdadaf44000a50 0x503fb5b5e880014a 0xf7ffffffe0039ffb 0xfefffffffc0073ff

def z1130 : W := mkw 0x0330037011b41504 0x2066006e023682a0 0xabf003f01ffc0002 0x157e007e03ff8000

def z1131 : W := mkw 0x80400c000c014a52 0x500801800180294a 0x71c80c0c1c03ffff 0xee39018183807fff

def z1132 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xabf00bf01ffc1f07 0x157e017e03ff83e0

def z1133 : W := mkw 0x0330025015b41f04 0x6066004a02b683e0 0xfbf00bc01ffc1f07 0x5f7e017803ff83e0

def z1134 : W := mkw 0x4000c2c501609420 0x88001858a02c1284 0x2e29c9cc03e19c63 0x05c53939807c338c

def z1135 : W := mkw 0x053370001adbe007 0x80a66e00035b7c00 0xfdf3f0001fffe007 0x1fbe7e0003fffc00

def z1136 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0x7be00dc01ffc1f07 0x4f7c01b803ff83e0

def z1137 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0x2e29c9cc03e18c62 0x05c53939807c318c

def z1138 : W := mkw 0x6002c2d5a36695a9 0xac00585ab46cd2b5 0xbe2bcbfde3e39ce3 0xf7c5797fbc7c739c

def z1139 : W := mkw 0x01fdadaf48014002 0x003fb5b5e9002800 0xf7fffffffc018002 0xfeffffffff803000

def z1140 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf23ff1fffc1f07 0x5f7e47fe3fff83e0

def z1141 : W := mkw 0x4002c2c503629421 0x88005858a06c5284 0xbe2bcbcc03e39c63 0x77c57979807c738c

def z1142 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xc7f7ffffe0000000 0xd8fefffffc000000

def z1143 : W := mkw 0x03712f7055b41f04 0x606e25ee0ab683e0 0xfbf03ff07ffc1f07 0x5f7e07fe0fff83e0

def z1144 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xd8163633e31c631c 0xfb02c6c67c638c63

def z1145 : W := mkw 0xe08ed08faa4be0fb 0x9c11da11f5497c1f 0x040ff00fe003e0f8 0xa081fe01fc007c1f

def z1146 : W := mkw 0x05bf70009adbe087 0x80b7ee00135b7c10 0xfdfff0019fffe087 0xbfbffe0033fffc10

def z1147 : W := mkw 0x80cc0d2a0c014a52 0x501981a54180294a 0x73cc0ffe1c03ffff 0xee7981ffc3807fff

def z1148 : W := mkw 0x26025250bfffff8f 0xe4c04a4a17fffff1 0x080000001fffff9f 0x0100000003fffff3

def z1149 : W := mkw 0x85bf700a1adbe057 0x90b7ee01435b7c0a 0xfdfff40e1ffff3ff 0xffbffe81c3fffe7f

def z1150 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xbe2bcfffe3ffffff 0xf7c579fffc7fffff

def z1151 : W := mkw 0x6002d2d5a36eb5a9 0xac005a5ab46dd6b5 0xbe2fffffe3e3fffb 0xf7c5fffffc7c7fff

def z1152 : W := mkw 0x05bd600018d1c006 0x80b7ac00031a3800 0xfdfdc0001fffe007 0x3fbfb80003fffc00

def z1153 : W := mkw 0x01fdadaf4c014a02 0x403fb5b5e9802940 0xf7fffffffc03ff07 0xfeffffffff807fe0

def z1154 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff0001ffff087 0xffbffe0003fffe10

def z1155 : W := mkw 0x0041adaf40000000 0x000835b5e8000000 0x0603ffffe0000000 0xc0c07ffffc000000

def z1156 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0xb63bfbfde0039ce3 0xf6c77f7fbc00739c

def z1157 : W := mkw 0x25bf7000badbe08f 0x84b7ee00175b7c11 0xfdfff403fffff39f 0xffbffe807ffffe73

def z1158 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x41cc040e1c03ffff 0xa8398081c3807fff

def z1159 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7ffffffe0001c03 0xfefffffffc000380

def z1160 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0x4bd00ff01ffc1f07 0x497a01fe03ff83e0

def z1161 : W := mkw 0x80cd2c0a0c014a52 0x5019a5814180294a 0x75cffc0e1c03ffff 0xeeb9ff81c3807fff

def z1162 : W := mkw 0x20021010220e2109 0x240042020441c421 0xd8163633e31e631d 0xfb02c6c67c63cc63

def z1163 : W := mkw 0x05bd700018d9e006 0x80b7ae00031b3c00 0xfdfdf0001ffde007 0x1fbfbe0003ffbc00

def z1164 : W := mkw 0x03700f6015b01e04 0x406e01ec02b603c0 0xfbf00bc01ffc1c07 0x5f7e017803ff8380

def z1165 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xbe29cbcc03e39ce3 0x57c53979807c739c

def z1166 : W := mkw 0x0171adaf40000000 0x002e35b5e8000000 0x8633f7f3e0000000 0x10c67efe7c000000

def z1167 : W := mkw 0x0533700012daa005 0x80a66e00025b5400 0xadf3f0001ffc0002 0x15be7e0003ff8000

def z1168 : W := mkw 0x64025250bbfff5af 0xac804a4a177ffeb5 0x080000001fffffff 0x0100000003ffffff

def z1169 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xae2bcbcd83e39ce3 0x15c57979b07c739c

def z1170 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdfff00c1fffe0e7 0xbfbffe0183fffc1c

def z1171 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf40ff01ffe7f07 0x7f7e81fe03ffcfe0

def z1172 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0x3629c9cc00e38c63 0x26c53939801c718c

def z1173 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xcdfff0001fffe004 0x39bffe0003fffc00

def z1174 : W := mkw 0x01bf600012d28005 0x8037ec00025a5000 0xfdfff0001fff8007 0x3fbffe0003fff000

def z1175 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7fffffffc03ec67 0xfeffffffff807d8c

def z1176 : W := mkw 0x01bd200010900004 0x0037a40002120000 0xfdf9c0001ffc0007 0x1fbf380003ff8000

def z1177 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0xb62bc9cc00e18c62 0x36c57939801c318c

def z1178 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7fffbfde0000000 0x3effff7fbc000000

def z1179 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xbe2bcbcd83e19c63 0x57c57979b07c338c

def z1180 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xabf00ff01ffc1f02 0x557e01fe03ff83e0

def z1181 : W := mkw 0x03700f7a55b41f04 0x606e01ef4ab683e0 0xfbf00ff27ffc1f07 0x5f7e01fe4fff83e0

def z1182 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf40ff21ffc1f07 0xff7e81fe43ff83e0

def z1183 : W := mkw 0x25bf70003adbe00f 0x84b7ee00075b7c01 0xfdfff0027fffe01f 0x3fbffe004ffffc03

def z1184 : W := mkw 0x4002c0c502628421 0x88005818a04c5084 0xbe2bcbcd83e38c63 0xf7c57979b07c718c

def z1185 : W := mkw 0x60021250a32e35a9 0x2c00424a1465c6b5 0xd8163633e31e7ffd 0xfb02c6c67c63cfff

def z1186 : W := mkw 0x81fdadaf48014052 0x103fb5b5e900280a 0xf7ffffffe003f3fd 0xfefffffffc007e7f

def z1187 : W := mkw 0x20001210a10c3188 0x2400024214218631 0xd0163633e01c739c 0xfa02c6c67c038e73

def z1188 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xf8363633e3fe739f 0xff06c6c67c7fce73

def z1189 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7fffffffc019ffa 0xfeffffffff8033ff

def z1190 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xbbf00bf01ffc1c03 0x577e017e03ff8380

def z1191 : W := mkw 0x45bf70009adbe0a7 0x88b7ee00135b7c14 0xfdfff0001fffe0e7 0x3fbffe0003fffc1c

def z1192 : W := mkw 0x80cd2c0a4c014a52 0x5019a5814980294a 0x71cc3c0e7c03ffff 0xee398781cf807fff

def z1193 : W := mkw 0x0171adaf40000000 0x002e35b5e8000000 0xf7f3ffffe0000000 0xdefe7ffffc000000

def z1194 : W := mkw 0x20021010a20e2189 0x240042021441c431 0x40163433e01c631c 0x0802c6867c038c63

def z1195 : W := mkw 0x20021250a32e3589 0x2400424a1465c6b1 0xfa3e3fffe3ffffff 0xff47c7fffc7fffff

def z1196 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0x8e2bcbcd83e39ce0 0xf1c57979b07c739c

def z1197 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xf9d63633ff1e739f 0xff3ac6c67fe3ce73

def z1198 : W := mkw 0x4002c0c5826284a1 0x88005818b04c5094 0xbe2bc9cd83e38ce3 0xb7c57939b07c719c

def z1199 : W := mkw 0x4002c2d5836695a1 0xa800585ab06cd2b4 0xbe2bcbcd83ff9fe7 0xf7c57979b07ff3fc

def z1200 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xc7f7f7f3fc00631c 0x18fefefe7f800c63

def z1201 : W := mkw 0x4002d2c5836ab4a1 0x88005a58b06d5694 0xbe2bcbcd83fffce7 0xf7c57979b07fff9c

def z1202 : W := mkw 0x4002d2c5836ab4a1 0x88005a58b06d5694 0xbe2ffbcd83e3fce3 0xf7c5ff79b07c7f9c

def z1203 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x31c8080c1c03ffff 0xe639010183807fff

def z1204 : W := mkw 0x20025250a36eb589 0xa4004a4a146dd6b1 0xfe3ffff3e3ffff9f 0xffc7fffe7c7ffff3

def z1205 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0xd633f7f1e0000000 0x5ac67efe3c000000

def z1206 : W := mkw 0x83700f7a15b41f54 0x706e01ef42b683ea 0xfbf80ffe1fff9fff 0xff7f01ffc3fff3ff

def z1207 : W := mkw 0x81bda1af48014052 0x1037b435e900280a 0x863ff3ffe003e0f8 0xb0c7fe7ffc007c1f

def z1208 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0x71ce3c0ffc03ffff 0xee39c781ff807fff

def z1209 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7fbfffde0000000 0x5eff7fffbc000000

def z1210 : W := mkw 0x4002c2d5836695a1 0xa800585ab06cd2b4 0xbe3bcbfd83ff9ce3 0xf7c7797fb07ff39c

def z1211 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdf9c0001fffe007 0x1fbf380003fffc00

def z1212 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xbe2bcfcf83e39ffb 0xf7c579f9f07c73ff

def z1213 : W := mkw 0x4002c2c5836294a1 0x88005858b06c5294 0xfe2fcfcf83e39ce3 0xffc5f9f9f07c739c

def z1214 : W := mkw 0x81fdadaf48014052 0x103fb5b5e900280a 0xf7ffffffe0006018 0xfefffffffc000c03

def z1215 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7ffffffe003fff8 0xfefffffffc007fff

def z1216 : W := mkw 0x23700f7035b41f0c 0x646e01ee06b683e1 0xfbf00ff27ffc1f1f 0x5f7e01fe4fff83e3

def z1217 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xfbf00ff01ffc0304 0x5f7e01fe03ff8060

def z1218 : W := mkw 0x83700f7a15b41f54 0x706e01ef42b683ea 0xfbf00ffc1ffc1f67 0x5f7e01ff83ff83ec

def z1219 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0xf9dc0c0e1f1fffff 0xff3b8181c3e3ffff

def z1220 : W := mkw 0x81fdadaf44000a50 0x503fb5b5e880014a 0xf7fffffffc001fff 0xfeffffffff8003ff

def z1221 : W := mkw 0x20021210a30e3189 0x240042421461c631 0x88163633e31e7398 0xf102c6c67c63ce73

def z1222 : W := mkw 0x23700f70b5b41f8c 0x646e01ee16b683f1 0xfbf40ff3fffe7f9f 0xff7e81fe7fffcff3

def z1223 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0xcbf007f01ffc1f07 0x197e00fe03ff83e0

def z1224 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xfdf7f0001ffc6007 0x1fbefe0003ff8c00

def z1225 : W := mkw 0x25bf7000badbe08f 0x84b7ee00175b7c11 0xfdfff001ffffe007 0x3fbffe003ffffc00

def z1226 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xf8163e33e31e7f9f 0xff02c7c67c63cff3

def z1227 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0x863bf3fde0000000 0xb0c77e7fbc000000

def z1228 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xa7fbffffe0000000 0xd4ff7ffffc000000

def z1229 : W := mkw 0xc48ff08f8a4be0f3 0x9891fe11f1497c1e 0x040ff00f8003e0f8 0xa081fe01f0007c1f

def z1230 : W := mkw 0x20021210a30e3189 0x240042421461c631 0xfc3ff633e31e739d 0xff87fec67c63ce73

def z1231 : W := mkw 0x01fdadaf44000a00 0x403fb5b5e8800140 0xf7ffffffe0001f00 0xfefffffffc0003e0

def z1232 : W := mkw 0x4000c2c5816094a0 0x88001858b02c1294 0x3629cbcd80e39ce3 0xe6c53979b01c739c

def z1233 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7fffffffc039ce3 0xfeffffffff80739c

def z1234 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0x6bf00df01ffc1f07 0x0d7e01be03ff83e0

def z1235 : W := mkw 0x4000c2c5816094a0 0x88001858b02c1294 0xb62bcbcd80e19ce2 0xf6c57979b01c339c

def z1236 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0x27efffffe0000000 0xe4fdfffffc000000

def z1237 : W := mkw 0x6002c2d5a36695a9 0xac00585ab46cd2b5 0xbe2bcbcd83e39ffb 0xf7c57979b07c73ff

def z1238 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0xedfff0001ffde006 0x1dbffe0003ffbc00

def z1239 : W := mkw 0x6002d2c5a36ab4a9 0x8c005a58b46d5695 0xbe2bcbcd83e3fcfb 0xf7c57979b07c7f9f

def z1240 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7f7fff3e0000000 0x5efefffe7c000000

def z1241 : W := mkw 0x0131a1a540000000 0x00263434a8000000 0xd637f3f1e0000000 0x3ac6fe7e3c000000

def z1242 : W := mkw 0x248ff08fea4be08b 0x8491fe11fd497c11 0x040ff00fe003e098 0xa081fe01fc007c13

def z1243 : W := mkw 0x03700f7a15b41f04 0x606e01ef42b683e0 0xfbf00ffe1ffc1f07 0xdf7e01ffc3ff83e0

def z1244 : W := mkw 0x008da1af40000000 0x0011b435e8000000 0x060ff3ffe0000000 0xa0c1fe7ffc000000

def z1245 : W := mkw 0x81fdadaf4c014a52 0x503fb5b5e980294a 0xf7fffffffc019f67 0xfeffffffff8033ec

def z1246 : W := mkw 0x808c00000c014a52 0x501180000180294a 0x71cc080c1c03ffff 0xee39810183807fff

def z1247 : W := mkw 0x05bf70001adbe007 0x80b7ee00035b7c00 0x2deff0001fffe007 0x25bdfe0003fffc00

def z1248 : W := mkw 0x03700f7015b41f04 0x606e01ee02b683e0 0x2be00ff01ffc1f07 0x457c01fe03ff83e0

def z1249 : W := mkw 0x4000c0c500608420 0x88001818a00c1084 0xb629cbcc00e18c62 0x56c53979801c318c

def z1250 : W := mkw 0x81fdadaf44000a50 0x503fb5b5e880014a 0xf7ffffffe0027ffd 0xfefffffffc004fff

def z1251 : W := mkw 0x80cc0c0a0c014a52 0x501981814180294a 0xf3ec0fce1c03ffff 0xfe7d81f9c3807fff

def z1252 : W := mkw 0x02408ff505241f00 0x604811fea0a483e0 0x02000ffd80001f00 0xc04001ffb00003e0

def z1253 : W := mkw 0x01fdadaf40000000 0x003fb5b5e8000000 0xf7ffffffe0026005 0xfefffffffc004c00

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z7,z5,z8,z6]),(0,[z2,z9,z3,z7,z5,z6,z10]),(1,[z2,z3,z7,z11,z6,z10]),(0,[z12,z1,z2,z3,z7,z13,z6]),(0,[z1,z2,z3,z7,z14,z5,z6]),(0,[z15,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z9,z3,z7,z11,z6]),(0,[z1,z2,z3,z7,z11,z6,z16]),(0,[z1,z2,z3,z7,z17,z18,z6])],[(0,[z1,z2,z3,z19,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z20]),(0,[z1,z3,z7,z5,z21,z6,z22]),(0,[z1,z23,z2,z3,z7,z5,z6])],[(0,[z24,z1,z2,z3,z7,z5,z6]),(0,[z25,z2,z3,z7,z5,z6,z10]),(0,[z1,z2,z26,z3,z7,z5,z6]),(0,[z27,z28,z2,z3,z7,z5,z6]),(1,[z29,z1,z2,z7,z5,z30]),(0,[z31,z1,z2,z3,z7,z17,z6])],[(0,[z1,z32,z2,z3,z7,z11,z6]),(0,[z2,z3,z7,z5,z33,z6,z10]),(0,[z1,z34,z35,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z36,z11,z6])],[(0,[z37,z38,z2,z3,z7,z5,z6]),(0,[z12,z1,z2,z3,z7,z11,z6]),(0,[z39,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z11,z40,z6])],[(0,[z1,z2,z3,z7,z5,z6,z41]),(0,[z37,z2,z3,z7,z5,z6,z10]),(0,[z42,z1,z2,z3,z7,z5,z6]),(0,[z1,z43,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z44,z7,z5,z6])],[(0,[z1,z2,z3,z7,z45,z5,z6]),(0,[z1,z2,z3,z7,z5,z46,z6]),(0,[z1,z2,z47,z7,z36,z5,z6]),(0,[z48,z1,z2,z3,z7,z5,z6]),(0,[z1,z49,z2,z3,z7,z5,z6]),(0,[z1,z2,z7,z36,z5,z6,z30])],[(0,[z1,z2,z3,z50,z7,z5,z6]),(1,[z2,z3,z7,z5,z6,z10]),(0,[z31,z37,z2,z3,z7,z5,z6]),(0,[z1,z2,z51,z3,z7,z5,z6]),(0,[z1,z2,z52,z3,z7,z5,z6]),(1,[z1,z2,z3,z53,z5,z6]),(0,[z1,z2,z54,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z55,z5,z6]),(0,[z1,z2,z3,z7,z5,z56,z6]),(0,[z1,z2,z3,z7,z5,z6,z57]),(0,[z1,z2,z3,z7,z5,z6,z16])]],
   [[(0,[z58,z2,z3,z7,z5,z6,z10]),(0,[z1,z2,z3,z59,z7,z5,z6]),(0,[z1,z2,z3,z60,z61,z5,z6]),(0,[z62,z1,z3,z7,z5,z21,z6]),(0,[z63,z1,z2,z3,z7,z5,z6])],[(0,[z64,z1,z2,z3,z7,z5,z6]),(0,[z2,z3,z7,z5,z65,z6,z10]),(0,[z1,z2,z3,z66,z7,z5,z6]),(1,[z1,z2,z3,z67,z11,z6]),(1,[z68,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z7,z11,z6,z69])],[(0,[z70,z1,z2,z3,z7,z5,z6]),(0,[z71,z72,z1,z2,z7,z5,z6]),(0,[z1,z2,z3,z73,z7,z5,z6]),(0,[z74,z1,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z7,z5,z6,z75]),(0,[z76,z1,z2,z3,z7,z5,z6])],[(0,[z1,z77,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z78,z5,z6]),(0,[z1,z2,z3,z7,z5,z79,z6]),(0,[z80,z37,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z17,z81,z6]),(0,[z1,z2,z3,z7,z82,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z83]),(0,[z84,z1,z2,z3,z7,z17,z6]),(0,[z25,z1,z2,z85,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z40,z6])],[(0,[z86,z1,z2,z3,z60,z5,z6]),(0,[z1,z2,z3,z7,z5,z87,z6]),(0,[z1,z34,z3,z7,z61,z5,z6]),(0,[z1,z34,z2,z3,z7,z5,z6])],[(0,[z1,z88,z2,z3,z7,z5,z6]),(1,[z0,z1,z2,z3,z11,z6]),(0,[z89,z2,z3,z7,z5,z6,z10]),(0,[z1,z38,z90,z3,z7,z5,z6]),(0,[z91,z1,z2,z7,z5,z21,z6])],[(0,[z1,z2,z3,z92,z7,z5,z6]),(0,[z1,z2,z3,z93,z7,z5,z6]),(0,[z2,z3,z7,z94,z5,z6,z10]),(0,[z2,z3,z7,z5,z11,z6,z10]),(0,[z1,z2,z3,z7,z5,z95,z6]),(1,[z25,z1,z2,z3,z5,z16]),(1,[z1,z2,z3,z7,z96,z33])],[(1,[z1,z2,z3,z7,z97,z6]),(0,[z12,z2,z3,z7,z5,z6,z10]),(0,[z1,z2,z3,z7,z98,z5,z6]),(0,[z1,z2,z3,z7,z5,z99,z6]),(0,[z1,z2,z3,z7,z5,z6,z100])]],
   [[(0,[z1,z2,z101,z3,z7,z5,z6]),(0,[z86,z2,z3,z7,z4,z5,z6]),(0,[z102,z1,z2,z3,z7,z5,z6]),(0,[z103,z1,z2,z3,z7,z11,z6]),(0,[z84,z37,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z104,z6]),(0,[z1,z2,z3,z7,z5,z6,z105]),(0,[z106,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z85,z7,z5,z6]),(0,[z1,z2,z3,z7,z96,z5,z69]),(0,[z1,z2,z3,z7,z5,z6,z69])],[(0,[z1,z107,z2,z3,z7,z5,z6])],[(0,[z108,z1,z2,z109,z7,z5,z6]),(0,[z110,z1,z2,z3,z7,z5,z6]),(1,[z0,z2,z3,z111,z5,z6]),(0,[z112,z72,z2,z3,z7,z5,z6]),(0,[z113,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z54,z7,z94,z6]),(1,[z114,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z115])],[(0,[z1,z2,z116,z3,z7,z5,z6]),(0,[z1,z117,z2,z3,z7,z5,z6]),(0,[z0,z2,z3,z111,z7,z5,z6]),(0,[z72,z1,z2,z7,z36,z5,z6]),(0,[z1,z2,z3,z118,z7,z5,z6]),(0,[z62,z1,z2,z3,z7,z11,z6]),(0,[z119,z1,z2,z3,z7,z5,z6]),(0,[z120,z1,z2,z3,z7,z5,z6])],[(0,[z2,z3,z7,z5,z21,z6,z10]),(1,[z28,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z121,z6]),(0,[z74,z2,z3,z7,z5,z6,z10]),(0,[z122,z1,z2,z3,z7,z5,z6]),(0,[z1,z3,z67,z7,z61,z5,z6]),(0,[z1,z2,z3,z7,z123,z5,z6]),(0,[z1,z124,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z6,z125]),(0,[z1,z2,z3,z7,z126,z5,z6]),(0,[z1,z2,z3,z7,z127,z5,z6]),(0,[z128,z1,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z7,z129,z5,z6]),(0,[z25,z1,z2,z3,z7,z130,z6])],[(0,[z1,z2,z3,z7,z5,z6,z131]),(0,[z1,z38,z3,z67,z7,z5,z6]),(0,[z132,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z133,z5,z40,z6])]],
   [[(0,[z134,z1,z2,z3,z7,z5,z6]),(0,[z37,z2,z3,z7,z135,z5,z6]),(0,[z136,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z137,z6]),(0,[z29,z1,z2,z3,z7,z17,z6])],[(0,[z1,z2,z3,z7,z5,z6,z138]),(0,[z1,z2,z139,z3,z7,z17,z6]),(0,[z1,z140,z3,z7,z5,z141,z6]),(0,[z1,z2,z3,z7,z11,z142,z6]),(1,[z2,z3,z7,z5,z6,z143]),(0,[z1,z2,z144,z3,z7,z5,z6])],[(1,[z71,z2,z47,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z145]),(0,[z37,z2,z51,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z146,z6]),(0,[z31,z1,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z7,z147,z5,z6])],[(0,[z103,z2,z3,z7,z5,z6,z10]),(0,[z148,z37,z2,z3,z7,z5,z6]),(0,[z1,z38,z2,z3,z61,z5,z6]),(1,[z1,z2,z3,z7,z130,z6])],[(0,[z74,z1,z2,z139,z7,z5,z6]),(0,[z1,z2,z3,z7,z149,z5,z6]),(1,[z2,z3,z7,z5,z56,z6]),(0,[z150,z1,z2,z3,z7,z5,z33])],[(0,[z1,z2,z151,z3,z7,z5,z6]),(0,[z37,z2,z3,z7,z5,z65,z6]),(0,[z29,z37,z2,z3,z7,z5,z6]),(0,[z152,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z11,z153,z6])],[(0,[z1,z2,z3,z7,z154,z5,z6]),(0,[z62,z2,z3,z7,z5,z6,z10]),(0,[z2,z3,z7,z5,z155,z6,z10]),(0,[z1,z2,z3,z156,z7,z5,z6]),(0,[z157,z1,z2,z3,z7,z5,z6]),(0,[z62,z1,z2,z3,z7,z21,z6]),(0,[z1,z2,z54,z3,z7,z11,z6])],[(0,[z86,z1,z2,z3,z7,z5,z158]),(0,[z1,z2,z3,z159,z7,z5,z6]),(0,[z1,z2,z160,z3,z7,z5,z6]),(0,[z161,z1,z2,z3,z7,z5,z6]),(0,[z37,z34,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z162,z6]),(0,[z1,z2,z3,z7,z94,z5,z6])]],
   [[(0,[z163,z1,z32,z3,z7,z5,z6]),(1,[z1,z164,z3,z7,z5,z6]),(0,[z165,z1,z2,z3,z7,z5,z6]),(1,[z166,z2,z3,z7,z167,z6]),(0,[z1,z2,z3,z7,z5,z168,z6]),(0,[z72,z1,z3,z169,z7,z5,z6]),(0,[z1,z2,z3,z7,z170,z5,z6]),(0,[z29,z1,z2,z9,z7,z5,z6]),(0,[z1,z2,z3,z7,z17,z5,z6]),(0,[z1,z2,z3,z7,z5,z142,z6]),(0,[z1,z2,z3,z60,z7,z17,z6])],[(0,[z171,z1,z2,z3,z7,z5,z6]),(0,[z172,z1,z2,z3,z7,z5,z6])],[(0,[z1,z173,z2,z3,z7,z5,z6]),(1,[z1,z2,z174,z7,z5,z6]),(0,[z2,z3,z67,z7,z5,z6,z10]),(0,[z2,z3,z175,z7,z5,z6,z10]),(0,[z1,z2,z3,z7,z5,z6,z176]),(0,[z1,z2,z3,z177,z7,z5,z6]),(0,[z178,z1,z2,z3,z7,z5,z6]),(0,[z2,z3,z7,z5,z65,z6,z83]),(0,[z25,z1,z2,z3,z7,z17,z6])],[(0,[z32,z2,z109,z3,z7,z5,z6]),(0,[z2,z3,z179,z7,z5,z6,z10]),(0,[z72,z1,z2,z7,z5,z6,z30]),(0,[z1,z2,z3,z180,z7,z5,z6]),(0,[z1,z2,z54,z3,z7,z181,z6]),(0,[z84,z1,z2,z3,z7,z11,z6])],[(0,[z1,z2,z3,z179,z7,z5,z6]),(0,[z86,z1,z2,z3,z111,z5,z6]),(0,[z1,z2,z3,z7,z5,z153,z6]),(0,[z1,z2,z3,z7,z5,z6,z182])],[(0,[z31,z2,z3,z7,z5,z6,z10]),(0,[z1,z2,z3,z7,z5,z183,z6]),(0,[z184,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z185,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z186]),(0,[z1,z2,z3,z7,z5,z6,z187]),(0,[z188,z1,z2,z3,z7,z11,z6])],[(0,[z1,z189,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z190,z7,z5,z6]),(0,[z1,z2,z3,z169,z7,z5,z6]),(0,[z1,z2,z3,z191,z7,z5,z6])],[(0,[z25,z37,z2,z3,z7,z5,z6]),(0,[z1,z192,z2,z3,z7,z5,z6])]],
   [[(0,[z58,z1,z2,z3,z7,z17,z6]),(0,[z1,z2,z3,z193,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z194]),(0,[z1,z34,z90,z3,z7,z5,z6]),(0,[z195,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z196,z5,z6]),(0,[z1,z2,z3,z7,z5,z197,z6])],[(0,[z1,z2,z3,z7,z5,z6,z6]),(0,[z2,z3,z7,z5,z141,z6,z10]),(0,[z198,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z199]),(0,[z1,z2,z3,z7,z96,z5,z6])],[(0,[z200,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z201,z7,z5,z6]),(0,[z1,z2,z3,z7,z202,z5,z6])],[(0,[z1,z2,z3,z7,z5,z203,z6]),(1,[z37,z2,z3,z7,z17,z6]),(0,[z1,z2,z3,z204,z7,z5,z6]),(0,[z1,z2,z3,z7,z11,z6,z22]),(0,[z25,z106,z2,z3,z7,z5,z6])],[(0,[z72,z1,z3,z7,z5,z6,z22]),(0,[z205,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z206]),(0,[z207,z1,z2,z3,z7,z5,z6]),(0,[z150,z1,z2,z3,z7,z6,z69])],[(1,[z208,z1,z3,z7,z5,z6]),(0,[z1,z2,z3,z175,z7,z5,z6]),(0,[z1,z2,z209,z3,z7,z5,z6])],[(0,[z1,z2,z3,z210,z7,z5,z6]),(0,[z1,z32,z2,z3,z7,z17,z6]),(0,[z84,z2,z3,z7,z5,z6,z10]),(0,[z1,z2,z3,z7,z5,z81,z16]),(0,[z1,z211,z2,z7,z36,z5,z6]),(0,[z27,z212,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z7,z213,z6]),(0,[z1,z2,z3,z7,z36,z17,z6])],[(0,[z134,z163,z2,z3,z7,z5,z6]),(0,[z134,z1,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z214,z7,z5,z6]),(0,[z12,z1,z2,z3,z7,z17,z6]),(0,[z1,z2,z139,z3,z36,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z5,z11,z6]),(0,[z1,z2,z3,z7,z5,z6,z215]),(0,[z216,z2,z3,z7,z5,z65,z6]),(0,[z1,z2,z3,z7,z5,z6,z217])],[(0,[z1,z2,z3,z218,z7,z5,z6]),(0,[z2,z3,z111,z7,z5,z6,z10]),(0,[z1,z2,z219,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z220,z6]),(0,[z1,z2,z139,z3,z7,z11,z6]),(0,[z1,z2,z3,z7,z5,z221,z6])],[(0,[z1,z2,z3,z7,z222,z5,z6]),(0,[z71,z1,z211,z2,z7,z5,z6]),(0,[z2,z139,z3,z7,z5,z6,z10]),(0,[z37,z2,z3,z7,z5,z162,z6]),(0,[z37,z2,z3,z7,z94,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z223]),(0,[z224,z1,z2,z3,z7,z5,z6]),(0,[z27,z1,z2,z3,z7,z5,z65]),(0,[z1,z2,z3,z7,z5,z6,z22]),(0,[z1,z2,z3,z7,z5,z225,z6]),(0,[z1,z226,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z227,z5,z6]),(0,[z228,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z229,z5,z6]),(0,[z1,z2,z3,z230,z7,z5,z6]),(0,[z1,z38,z2,z3,z7,z17,z6]),(0,[z1,z231,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z232,z6]),(0,[z1,z2,z233,z3,z7,z5,z6]),(0,[z150,z1,z209,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z234])],[(0,[z134,z32,z2,z3,z7,z5,z6]),(0,[z12,z37,z2,z3,z7,z5,z6]),(0,[z235,z1,z2,z3,z7,z5,z6]),(0,[z236,z1,z2,z3,z7,z5,z6]),(0,[z25,z1,z2,z3,z7,z237,z6])],[(0,[z238,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z7,z239,z6]),(0,[z74,z1,z2,z3,z7,z17,z6]),(0,[z1,z2,z3,z240,z60,z5,z6]),(0,[z25,z1,z241,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z242,z6])],[(0,[z1,z2,z3,z7,z243,z5,z6]),(0,[z37,z2,z3,z179,z7,z5,z6]),(0,[z1,z2,z174,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z244]),(0,[z1,z2,z3,z7,z17,z11,z6])]],
   [[(0,[z1,z2,z3,z7,z245,z5,z6]),(0,[z1,z2,z3,z7,z5,z246,z6]),(0,[z1,z2,z3,z7,z5,z247,z6]),(0,[z1,z2,z3,z60,z7,z11,z6])],[(0,[z163,z2,z109,z3,z7,z5,z6]),(0,[z248,z1,z2,z3,z7,z5,z6]),(0,[z166,z1,z2,z3,z7,z5,z6]),(0,[z37,z2,z3,z169,z7,z5,z6]),(0,[z249,z1,z2,z3,z7,z5,z6]),(0,[z1,z250,z2,z3,z7,z5,z6]),(0,[z251,z1,z2,z3,z7,z17,z6]),(1,[z1,z2,z3,z7,z237,z6])],[(0,[z72,z163,z1,z3,z7,z5,z6]),(0,[z134,z2,z3,z7,z5,z6,z10]),(0,[z252,z1,z2,z3,z7,z5,z6]),(0,[z74,z37,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z253]),(0,[z1,z35,z3,z7,z5,z6,z22]),(0,[z254,z1,z2,z3,z7,z5,z6]),(1,[z1,z241,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z255,z6]),(0,[z29,z2,z3,z7,z5,z6,z10]),(0,[z37,z1,z2,z3,z7,z5,z81]),(0,[z1,z2,z54,z3,z7,z94,z6]),(0,[z150,z1,z2,z3,z256,z5,z6])],[(0,[z1,z2,z257,z3,z7,z5,z6]),(0,[z37,z2,z3,z7,z96,z5,z6]),(0,[z258,z1,z2,z3,z7,z5,z6]),(0,[z74,z1,z2,z3,z7,z213,z6]),(0,[z1,z2,z3,z36,z5,z11,z6]),(0,[z1,z2,z3,z7,z17,z181,z6]),(1,[z192,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z259,z6]),(0,[z1,z2,z3,z7,z5,z6,z260]),(0,[z261,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z6,z262]),(0,[z86,z1,z2,z3,z7,z5,z125]),(0,[z1,z211,z2,z7,z5,z6,z30]),(0,[z62,z1,z2,z3,z7,z17,z6]),(0,[z1,z2,z3,z7,z56,z11,z6]),(0,[z1,z2,z3,z7,z5,z263,z6]),(0,[z25,z1,z2,z3,z133,z5,z6])],[(0,[z208,z1,z2,z3,z7,z5,z6]),(0,[z37,z264,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z265,z5,z6]),(0,[z2,z3,z7,z5,z6,z6,z10]),(0,[z1,z2,z266,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z267,z6]),(0,[z268,z1,z2,z3,z7,z5,z6]),(0,[z269,z1,z2,z3,z7,z94,z6])]],
   [[(0,[z2,z47,z3,z7,z5,z6,z10]),(0,[z1,z2,z3,z7,z5,z270,z6]),(0,[z1,z2,z3,z7,z271,z5,z6])],[],[(0,[z1,z2,z3,z7,z272,z5,z6]),(0,[z273,z37,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z17,z21,z6]),(0,[z274,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z275,z6])],[(0,[z276,z1,z2,z3,z7,z5,z6]),(0,[z71,z1,z2,z47,z7,z5,z6]),(0,[z62,z37,z2,z3,z7,z5,z6]),(1,[z37,z2,z3,z7,z11,z6])],[(0,[z2,z3,z111,z7,z135,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z277]),(0,[z278,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z9,z7,z36,z5,z6]),(0,[z279,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z6,z280]),(0,[z1,z2,z281,z3,z7,z5,z6]),(0,[z2,z3,z7,z61,z5,z6,z10]),(0,[z37,z2,z3,z7,z5,z6,z22]),(0,[z1,z2,z282,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z18,z6])],[(0,[z283,z1,z2,z3,z7,z5,z6]),(0,[z1,z284,z2,z3,z7,z5,z6]),(0,[z72,z1,z2,z7,z94,z5,z6]),(0,[z1,z2,z285,z3,z7,z5,z6]),(0,[z286,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z11,z65,z6]),(0,[z287,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z288,z3,z7,z5,z6]),(0,[z1,z2,z139,z240,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z6,z289]),(0,[z0,z1,z2,z3,z7,z17,z6]),(0,[z166,z2,z3,z111,z7,z5,z6]),(0,[z27,z1,z3,z7,z5,z6,z22]),(1,[z1,z231,z3,z7,z5,z6]),(0,[z269,z1,z2,z54,z7,z5,z6]),(0,[z1,z2,z3,z7,z181,z11,z6]),(0,[z1,z2,z3,z7,z5,z6,z290]),(0,[z1,z2,z7,z5,z141,z6,z30]),(0,[z1,z2,z3,z7,z5,z6,z143]),(0,[z1,z2,z3,z7,z291,z5,z6])]],
   [[(0,[z0,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z135,z5,z6]),(0,[z1,z2,z3,z292,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z293]),(0,[z1,z294,z2,z3,z7,z5,z6]),(0,[z1,z295,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z11,z296,z6])],[(0,[z24,z37,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z11,z81,z6]),(1,[z12,z1,z3,z61,z5,z6]),(0,[z1,z34,z38,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z297,z5,z6]),(0,[z1,z2,z3,z7,z5,z298,z6]),(0,[z1,z2,z54,z3,z7,z17,z6]),(0,[z299,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z300,z6]),(0,[z2,z3,z7,z5,z6,z10,z30]),(0,[z37,z301,z2,z3,z7,z5,z6])],[(0,[z163,z1,z109,z3,z7,z5,z6]),(0,[z302,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z303,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z10,z16]),(0,[z37,z2,z3,z7,z61,z5,z6]),(0,[z304,z1,z2,z3,z7,z5,z6]),(0,[z1,z38,z2,z3,z7,z11,z6]),(0,[z74,z1,z2,z3,z36,z5,z6])],[(0,[z305,z1,z2,z3,z7,z5,z6]),(0,[z86,z1,z2,z3,z4,z5,z6]),(0,[z1,z2,z3,z7,z4,z5,z6]),(0,[z306,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z307,z7,z5,z6]),(0,[z150,z308,z2,z3,z7,z5,z6])],[(0,[z72,z1,z2,z169,z7,z5,z6]),(0,[z309,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z65,z6])],[(0,[z1,z2,z3,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z310,z6]),(0,[z1,z34,z2,z3,z7,z17,z6]),(0,[z269,z1,z2,z3,z7,z5,z6]),(0,[z311,z1,z2,z3,z7,z5,z6])],[(0,[z312,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z296,z6]),(0,[z1,z2,z3,z313,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z314]),(0,[z1,z2,z3,z7,z5,z315,z6])]],
   [[(0,[z1,z2,z3,z7,z316,z5,z6]),(0,[z317,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z81,z6]),(0,[z72,z1,z34,z3,z7,z5,z6]),(0,[z1,z2,z3,z67,z7,z318,z6]),(1,[z27,z1,z3,z7,z5,z22])],[(0,[z86,z1,z2,z3,z7,z5,z6]),(0,[z103,z1,z2,z3,z7,z5,z81]),(0,[z319,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z11,z6,z16])],[(0,[z1,z2,z3,z7,z5,z320,z6]),(0,[z1,z2,z3,z7,z321,z5,z6]),(0,[z150,z1,z2,z3,z7,z96,z6])],[(0,[z71,z58,z2,z3,z7,z5,z6]),(0,[z1,z322,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z323,z6]),(0,[z1,z2,z3,z324,z7,z5,z6]),(0,[z325,z1,z2,z3,z7,z5,z6]),(1,[z2,z3,z7,z56,z11,z6]),(0,[z25,z1,z2,z3,z5,z6,z16])],[(0,[z1,z2,z90,z3,z7,z5,z6]),(0,[z1,z2,z3,z326,z7,z5,z6]),(0,[z327,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z36,z11,z6]),(0,[z110,z1,z2,z3,z7,z17,z6]),(0,[z328,z1,z2,z3,z7,z5,z6])],[(0,[z329,z1,z2,z3,z7,z5,z6]),(0,[z35,z2,z3,z7,z5,z6,z10]),(0,[z2,z3,z7,z5,z6,z10,z16]),(1,[z74,z1,z2,z36,z5,z6])],[(0,[z330,z1,z2,z3,z7,z5,z6]),(0,[z331,z1,z2,z3,z7,z5,z6])],[(1,[z1,z332,z3,z7,z5,z6]),(0,[z1,z333,z2,z3,z7,z5,z6]),(0,[z1,z2,z334,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z335,z6]),(0,[z1,z124,z2,z3,z7,z17,z6])]],
   [[(0,[z37,z2,z109,z3,z7,z5,z6]),(0,[z336,z1,z2,z3,z7,z5,z6]),(0,[z1,z34,z2,z3,z7,z5,z22]),(1,[z1,z2,z337,z7,z5,z6]),(0,[z1,z2,z3,z7,z126,z17,z6]),(0,[z1,z2,z85,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z338,z6]),(0,[z1,z2,z3,z339,z135,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z340])],[(0,[z163,z1,z90,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z341,z6]),(0,[z134,z1,z2,z3,z7,z17,z6]),(0,[z342,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z343,z7,z5,z6]),(0,[z344,z1,z2,z3,z7,z5,z6]),(0,[z345,z1,z2,z3,z7,z5,z6]),(1,[z91,z1,z2,z7,z5,z6])],[(1,[z58,z2,z179,z7,z5,z6]),(0,[z1,z2,z3,z7,z346,z5,z6]),(0,[z37,z2,z3,z292,z7,z5,z6]),(0,[z1,z34,z3,z7,z5,z21,z6]),(0,[z1,z2,z3,z7,z5,z6,z347])],[(1,[z1,z2,z3,z5,z79,z6]),(0,[z1,z2,z3,z7,z348,z5,z6]),(1,[z1,z2,z3,z256,z5,z6])],[(0,[z1,z2,z3,z7,z349,z5,z6]),(0,[z1,z2,z350,z3,z7,z5,z6]),(0,[z1,z2,z288,z3,z7,z11,z6])],[(0,[z1,z2,z3,z351,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z352]),(0,[z2,z3,z7,z5,z6,z10,z69]),(0,[z1,z2,z353,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z17,z141,z6])],[(0,[z134,z37,z2,z3,z7,z5,z6]),(0,[z1,z2,z354,z3,z7,z5,z6]),(0,[z37,z2,z3,z7,z4,z5,z6]),(0,[z0,z1,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z7,z135,z11,z6]),(0,[z2,z3,z7,z17,z5,z6,z10]),(0,[z1,z2,z3,z355,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z356,z6])]],
   [[(1,[z1,z357,z3,z7,z5,z6]),(0,[z264,z1,z2,z3,z7,z5,z6]),(1,[z2,z3,z7,z5,z10,z16]),(0,[z358,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z221,z11,z6]),(0,[z359,z1,z2,z3,z7,z5,z6])],[(0,[z2,z3,z169,z7,z5,z6,z10]),(0,[z360,z1,z2,z3,z7,z5,z6]),(0,[z1,z211,z2,z7,z94,z5,z6]),(0,[z62,z1,z2,z3,z53,z5,z6]),(0,[z1,z2,z3,z7,z94,z17,z6]),(0,[z1,z2,z9,z3,z7,z5,z141]),(0,[z2,z3,z7,z5,z56,z11,z6]),(1,[z361,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z362,z6]),(0,[z1,z363,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z17,z17,z6])],[(0,[z166,z2,z3,z7,z5,z167,z6]),(0,[z37,z2,z3,z7,z5,z81,z6]),(1,[z1,z2,z3,z7,z364,z6]),(0,[z1,z3,z7,z5,z141,z6,z365]),(0,[z1,z2,z3,z7,z366,z11,z6]),(0,[z1,z2,z3,z133,z7,z197,z6]),(0,[z1,z2,z3,z7,z5,z367,z6])],[(0,[z1,z109,z3,z7,z61,z5,z6]),(0,[z368,z1,z2,z3,z7,z5,z6]),(0,[z38,z2,z3,z7,z5,z6,z10])],[(0,[z58,z1,z211,z2,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z5,z6]),(0,[z1,z2,z3,z7,z5,z369,z6]),(0,[z1,z2,z3,z7,z370,z5,z6]),(0,[z269,z1,z2,z3,z7,z11,z6]),(0,[z371,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z372,z6]),(0,[z1,z2,z3,z179,z7,z17,z6]),(0,[z1,z34,z2,z3,z7,z11,z6]),(1,[z1,z2,z3,z7,z373,z6]),(0,[z1,z2,z3,z7,z374,z5,z6])],[(0,[z375,z1,z2,z3,z7,z5,z6]),(0,[z376,z1,z2,z3,z7,z5,z6]),(0,[z37,z2,z90,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z377,z6])]],
   [[(1,[z322,z2,z3,z7,z5,z6]),(0,[z1,z211,z2,z169,z7,z5,z6]),(0,[z1,z2,z3,z169,z7,z17,z6]),(0,[z1,z2,z3,z7,z378,z5,z6]),(0,[z1,z2,z3,z379,z7,z5,z6])],[(0,[z1,z211,z90,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z380,z5,z6]),(0,[z1,z2,z3,z7,z5,z381,z6])],[(0,[z1,z2,z3,z7,z5,z382,z6]),(0,[z0,z2,z3,z7,z5,z6,z10]),(0,[z269,z1,z2,z3,z7,z181,z6]),(0,[z1,z2,z3,z60,z17,z5,z6])],[(0,[z71,z2,z109,z3,z7,z5,z6]),(0,[z383,z1,z2,z3,z7,z5,z6]),(0,[z384,z1,z2,z3,z7,z5,z6]),(0,[z27,z1,z34,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z385,z6]),(0,[z1,z2,z3,z7,z377,z11,z6])],[(0,[z1,z386,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z202,z17,z6])],[(0,[z387,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z388]),(0,[z1,z2,z3,z7,z5,z6,z389]),(0,[z1,z2,z3,z390,z7,z5,z6]),(1,[z308,z2,z3,z7,z5,z6])],[(0,[z391,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z392,z5,z6]),(0,[z1,z393,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z394,z6]),(0,[z1,z212,z2,z3,z7,z5,z6])],[(0,[z72,z1,z38,z3,z7,z5,z6]),(1,[z1,z2,z3,z118,z5,z6]),(0,[z1,z2,z3,z395,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z396,z6])]],
   [[(0,[z397,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z339,z5,z6]),(0,[z269,z2,z3,z7,z5,z6,z10])],[(0,[z2,z109,z3,z7,z5,z6,z10]),(0,[z37,z2,z3,z7,z398,z5,z6]),(0,[z74,z1,z2,z3,z7,z364,z6]),(0,[z1,z2,z3,z7,z5,z6,z399])],[(1,[z108,z1,z2,z7,z5,z6]),(0,[z2,z47,z3,z179,z7,z5,z6]),(0,[z1,z2,z400,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z17,z33,z6]),(0,[z1,z2,z3,z7,z5,z6,z401])],[(0,[z1,z2,z3,z7,z5,z402,z6]),(0,[z1,z2,z3,z7,z5,z81,z40])],[(0,[z1,z403,z2,z3,z7,z5,z6]),(0,[z1,z2,z179,z7,z36,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z404]),(0,[z2,z3,z7,z5,z6,z10,z405]),(0,[z406,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z407,z6])],[(0,[z408,z1,z2,z3,z7,z5,z6]),(0,[z2,z3,z7,z4,z5,z6,z10]),(0,[z72,z1,z2,z3,z7,z5,z6]),(0,[z72,z1,z3,z7,z61,z5,z6]),(0,[z1,z231,z3,z240,z7,z5,z6]),(0,[z1,z2,z3,z409,z7,z5,z6]),(0,[z1,z2,z3,z7,z11,z11,z6])],[(0,[z58,z1,z2,z47,z7,z5,z6]),(0,[z410,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z180,z5,z6])],[(0,[z264,z1,z2,z3,z7,z11,z6]),(1,[z1,z2,z266,z7,z5,z6]),(0,[z150,z1,z2,z3,z291,z5,z6])]],
   [[(0,[z1,z357,z2,z3,z7,z5,z6]),(0,[z1,z2,z411,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z13,z6]),(0,[z1,z2,z3,z412,z7,z5,z6])],[(0,[z1,z2,z413,z3,z7,z5,z6]),(0,[z1,z2,z3,z60,z36,z5,z6]),(1,[z1,z2,z3,z196,z5,z6]),(0,[z1,z2,z3,z7,z94,z11,z6]),(0,[z1,z2,z9,z3,z7,z5,z30])],[(0,[z1,z2,z3,z7,z5,z414,z6]),(0,[z1,z301,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z415,z6]),(0,[z1,z2,z3,z7,z5,z416,z6]),(0,[z25,z192,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z417,z7,z5,z6]),(0,[z1,z2,z418,z3,z7,z5,z6])],[(0,[z1,z2,z2,z3,z7,z5,z6]),(0,[z37,z2,z47,z3,z7,z5,z6]),(0,[z1,z2,z419,z3,z7,z5,z6]),(0,[z166,z1,z2,z3,z7,z17,z6]),(0,[z72,z1,z211,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z61,z5,z6]),(0,[z1,z2,z3,z420,z7,z5,z6]),(0,[z1,z2,z3,z7,z421,z5,z6]),(0,[z31,z1,z2,z3,z60,z5,z6]),(0,[z1,z2,z3,z7,z96,z33,z6])],[(0,[z422,z1,z2,z3,z7,z5,z6]),(0,[z86,z1,z2,z3,z5,z11,z6]),(0,[z1,z2,z3,z7,z5,z6,z423]),(0,[z1,z2,z3,z7,z5,z11,z6]),(0,[z1,z2,z3,z5,z40,z6,z16])],[(0,[z58,z2,z3,z179,z7,z5,z6]),(0,[z86,z1,z2,z3,z7,z321,z6]),(1,[z112,z2,z3,z7,z5,z6]),(0,[z74,z1,z2,z3,z240,z5,z6])],[(0,[z1,z2,z3,z7,z5,z6,z424]),(0,[z1,z2,z3,z179,z7,z11,z6]),(0,[z1,z2,z3,z7,z5,z6,z425]),(0,[z34,z2,z3,z7,z5,z6,z10]),(0,[z426,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z427,z5,z6]),(0,[z72,z58,z1,z2,z7,z5,z6]),(0,[z1,z2,z3,z60,z133,z5,z6])]],
   [[(0,[z1,z2,z3,z7,z5,z428,z6]),(0,[z1,z2,z3,z429,z7,z5,z6]),(0,[z166,z37,z2,z3,z7,z5,z6]),(0,[z72,z1,z2,z90,z7,z5,z6]),(0,[z1,z2,z3,z169,z7,z11,z6]),(0,[z12,z1,z2,z3,z7,z239,z6])],[(0,[z163,z1,z2,z3,z7,z5,z6]),(0,[z86,z1,z2,z3,z7,z320,z6]),(0,[z1,z2,z3,z7,z5,z155,z6]),(0,[z1,z2,z3,z7,z5,z430,z6]),(0,[z1,z2,z3,z240,z7,z373,z6]),(0,[z269,z1,z2,z7,z5,z181,z6]),(0,[z1,z2,z3,z7,z5,z181,z6]),(0,[z1,z2,z3,z7,z5,z6,z431]),(0,[z150,z1,z2,z432,z7,z5,z6]),(0,[z150,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z433])],[(0,[z434,z1,z2,z3,z7,z5,z6]),(0,[z264,z2,z3,z7,z5,z6,z10]),(0,[z435,z1,z2,z3,z7,z5,z6]),(0,[z436,z1,z2,z3,z7,z5,z6])],[(0,[z37,z58,z2,z3,z7,z5,z6]),(0,[z2,z3,z7,z5,z6,z10,z10]),(0,[z1,z35,z2,z3,z7,z5,z6]),(1,[z212,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z96,z11,z6]),(0,[z1,z437,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z17,z40,z6])],[(0,[z1,z2,z3,z7,z438,z5,z6]),(0,[z1,z2,z3,z439,z7,z5,z6]),(0,[z440,z1,z2,z3,z7,z5,z6]),(0,[z161,z2,z3,z7,z5,z6,z10]),(1,[z37,z2,z3,z7,z5,z81]),(0,[z72,z1,z3,z7,z441,z5,z6]),(0,[z1,z2,z3,z7,z442,z5,z6]),(0,[z29,z1,z2,z7,z5,z6,z30]),(0,[z1,z2,z3,z7,z11,z443,z6])],[(0,[z1,z164,z3,z179,z7,z5,z6]),(0,[z1,z2,z3,z7,z444,z5,z6]),(0,[z1,z2,z139,z7,z5,z6,z30]),(0,[z1,z445,z2,z3,z7,z5,z6])],[(0,[z1,z446,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z447,z5,z6]),(0,[z1,z2,z3,z448,z7,z5,z6]),(0,[z62,z1,z2,z3,z118,z5,z6]),(1,[z1,z2,z7,z5,z449,z6]),(0,[z279,z1,z2,z3,z7,z17,z6]),(0,[z1,z2,z3,z7,z5,z450,z6]),(0,[z1,z451,z2,z3,z7,z5,z6])],[(0,[z1,z2,z109,z3,z7,z17,z6]),(0,[z452,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z453,z7,z5,z6]),(0,[z1,z2,z3,z7,z454,z5,z6]),(0,[z86,z1,z2,z439,z7,z5,z6]),(0,[z1,z2,z3,z7,z167,z11,z6]),(0,[z2,z3,z7,z5,z6,z455,z10]),(0,[z37,z2,z3,z7,z5,z33,z6]),(0,[z1,z2,z3,z7,z456,z5,z6]),(0,[z1,z2,z3,z7,z457,z5,z6]),(0,[z1,z2,z3,z7,z5,z21,z6]),(0,[z1,z2,z458,z3,z7,z5,z6]),(0,[z2,z3,z7,z5,z141,z6,z459]),(0,[z1,z2,z3,z7,z460,z5,z6])]],
   [[(0,[z1,z2,z109,z3,z7,z5,z6]),(1,[z86,z2,z3,z4,z5,z6]),(0,[z1,z2,z461,z3,z7,z5,z6]),(0,[z462,z1,z2,z3,z7,z5,z6]),(0,[z436,z1,z3,z7,z5,z181,z6]),(1,[z1,z2,z3,z17,z11,z6])],[(0,[z71,z1,z2,z179,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z463]),(0,[z68,z2,z3,z7,z5,z11,z6])],[(0,[z1,z2,z3,z7,z5,z6,z464]),(0,[z1,z2,z3,z7,z441,z5,z6]),(0,[z1,z2,z465,z3,z7,z5,z6])],[(0,[z2,z3,z111,z7,z4,z5,z6]),(0,[z2,z354,z3,z7,z5,z6,z10]),(0,[z1,z2,z3,z7,z5,z443,z6]),(0,[z1,z466,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z240,z7,z232,z6]),(0,[z29,z445,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z297,z17,z6])],[(0,[z72,z1,z2,z3,z7,z11,z6])],[(0,[z467,z1,z2,z3,z7,z5,z6]),(0,[z37,z2,z3,z240,z7,z5,z6]),(0,[z468,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z469,z6]),(0,[z1,z2,z3,z7,z5,z470,z6]),(0,[z1,z2,z471,z3,z7,z5,z6]),(0,[z1,z2,z3,z472,z7,z5,z6])],[(0,[z71,z2,z47,z3,z7,z5,z6]),(0,[z86,z1,z2,z174,z7,z5,z6]),(0,[z1,z2,z3,z7,z4,z17,z6]),(0,[z1,z473,z2,z3,z7,z5,z6]),(0,[z1,z35,z2,z3,z7,z441,z6]),(0,[z1,z2,z3,z7,z474,z5,z6])],[(0,[z1,z2,z3,z7,z475,z5,z6]),(0,[z1,z2,z476,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z97,z6]),(0,[z37,z2,z3,z7,z5,z11,z6]),(0,[z1,z2,z3,z7,z5,z6,z477]),(0,[z1,z2,z3,z7,z373,z5,z6]),(0,[z1,z478,z2,z3,z7,z5,z6])]],
   [[(0,[z1,z2,z3,z7,z479,z5,z6]),(0,[z1,z211,z2,z3,z7,z5,z6]),(0,[z27,z1,z2,z3,z7,z5,z6]),(0,[z269,z1,z2,z3,z7,z17,z6])],[(0,[z1,z2,z3,z7,z5,z6,z480]),(0,[z1,z90,z3,z169,z7,z5,z6]),(0,[z91,z1,z2,z3,z7,z5,z6]),(0,[z74,z1,z2,z7,z36,z5,z6]),(0,[z29,z1,z2,z3,z7,z5,z141])],[(0,[z1,z2,z3,z7,z61,z11,z6]),(0,[z1,z2,z266,z67,z7,z5,z6]),(0,[z481,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z482,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z483,z6])],[(0,[z484,z1,z2,z3,z7,z5,z6]),(0,[z86,z1,z2,z3,z7,z17,z6]),(0,[z166,z1,z2,z3,z7,z11,z6]),(0,[z485,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z486,z5,z6]),(0,[z1,z2,z3,z7,z487,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z459]),(0,[z1,z2,z3,z488,z7,z5,z6])],[(0,[z1,z2,z3,z7,z7,z5,z6]),(0,[z37,z2,z3,z7,z5,z181,z6]),(0,[z1,z2,z3,z489,z7,z5,z6]),(1,[z1,z2,z3,z7,z318,z6]),(0,[z1,z2,z3,z60,z5,z6,z16])],[(0,[z490,z1,z2,z3,z7,z5,z6]),(0,[z491,z1,z2,z3,z7,z5,z6]),(0,[z492,z1,z2,z3,z7,z5,z6]),(0,[z269,z37,z2,z3,z7,z5,z6]),(0,[z1,z2,z337,z7,z5,z65,z6]),(0,[z493,z1,z2,z3,z7,z5,z6]),(0,[z426,z1,z2,z3,z7,z11,z6])],[(0,[z2,z3,z7,z5,z81,z6,z10]),(0,[z37,z35,z2,z3,z7,z5,z6]),(0,[z1,z2,z90,z3,z7,z17,z6]),(0,[z1,z2,z3,z7,z318,z5,z6]),(0,[z1,z2,z337,z3,z7,z5,z6]),(0,[z494,z1,z2,z3,z7,z5,z6])],[(0,[z72,z2,z3,z7,z5,z6,z10]),(0,[z1,z2,z3,z7,z5,z495,z6]),(1,[z1,z209,z3,z7,z5,z6])]],
   [[(0,[z163,z1,z2,z3,z7,z11,z6]),(0,[z86,z37,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z17,z135,z6]),(0,[z1,z2,z3,z7,z496,z5,z6]),(0,[z497,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z139,z240,z5,z6]),(0,[z1,z2,z498,z3,z7,z5,z6]),(1,[z1,z2,z3,z291,z5,z6])],[(0,[z499,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z61,z5,z11,z6])],[(0,[z1,z2,z3,z7,z5,z6,z500]),(0,[z1,z2,z3,z501,z7,z5,z6]),(0,[z238,z2,z3,z7,z5,z6,z10]),(0,[z37,z2,z3,z7,z5,z21,z6]),(0,[z502,z1,z2,z3,z7,z5,z6]),(1,[z445,z2,z3,z7,z5,z6]),(0,[z68,z1,z2,z3,z7,z5,z6]),(0,[z1,z503,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z111,z7,z5,z6]),(0,[z504,z1,z2,z3,z7,z5,z6]),(0,[z2,z3,z7,z5,z168,z6,z10]),(1,[z72,z1,z169,z7,z5,z6]),(0,[z1,z211,z2,z90,z7,z5,z6]),(0,[z1,z2,z3,z505,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z506]),(0,[z359,z2,z3,z7,z5,z40,z6])],[(0,[z507,z1,z2,z3,z7,z5,z6]),(0,[z1,z508,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z11,z141,z6]),(0,[z344,z1,z2,z3,z7,z17,z6]),(0,[z1,z2,z509,z3,z7,z5,z6]),(0,[z361,z2,z3,z7,z5,z33,z6])],[(0,[z2,z3,z7,z5,z181,z6,z10]),(0,[z2,z3,z7,z5,z40,z6,z10]),(0,[z37,z2,z3,z7,z441,z5,z6]),(0,[z1,z90,z3,z7,z5,z6,z22]),(1,[z1,z2,z3,z133,z11,z6])],[(0,[z510,z1,z2,z3,z7,z5,z6]),(0,[z511,z1,z2,z3,z7,z5,z6]),(1,[z86,z1,z2,z3,z11,z6]),(0,[z1,z2,z3,z7,z512,z5,z6]),(0,[z166,z2,z3,z7,z5,z6,z10]),(0,[z72,z1,z2,z139,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z513,z6]),(0,[z514,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z7,z5,z65,z6,z217]),(0,[z1,z2,z3,z515,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z516])],[(0,[z1,z2,z109,z3,z7,z11,z6]),(0,[z1,z2,z9,z54,z7,z5,z6]),(1,[z1,z2,z3,z60,z17,z6]),(0,[z1,z2,z3,z7,z517,z5,z6])]],
   [[(0,[z37,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z133,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z518,z6]),(0,[z1,z2,z3,z7,z519,z5,z6]),(0,[z1,z2,z520,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z398,z5,z6]),(0,[z521,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z67,z7,z5,z6]),(0,[z522,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z523])],[(0,[z1,z2,z3,z7,z5,z524,z6]),(0,[z264,z1,z2,z3,z7,z17,z6]),(1,[z436,z1,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z525]),(1,[z1,z2,z432,z7,z5,z6])],[(0,[z163,z2,z3,z7,z5,z6,z10]),(0,[z2,z109,z3,z179,z7,z5,z6]),(0,[z1,z2,z3,z7,z526,z5,z6]),(0,[z37,z211,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z141,z6])],[(0,[z108,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z139,z3,z240,z5,z6]),(1,[z269,z1,z2,z7,z181,z6])],[(0,[z527,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z528,z7,z5,z6]),(0,[z1,z2,z3,z339,z7,z5,z6]),(0,[z2,z3,z7,z36,z5,z6,z10]),(0,[z269,z72,z1,z2,z7,z5,z6]),(0,[z1,z2,z3,z67,z7,z381,z6])],[(0,[z1,z2,z3,z7,z4,z11,z6]),(0,[z2,z3,z7,z96,z5,z6,z10]),(0,[z1,z2,z9,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z6,z529]),(0,[z2,z54,z3,z7,z5,z6,z10]),(1,[z1,z2,z9,z7,z5,z141]),(0,[z1,z2,z3,z256,z7,z5,z6])]],
   [[(0,[z89,z1,z2,z3,z7,z5,z6]),(0,[z1,z38,z3,z7,z5,z6,z22]),(1,[z2,z3,z7,z5,z6,z459]),(0,[z1,z2,z3,z7,z530,z5,z6]),(1,[z1,z2,z3,z7,z197,z6])],[(0,[z2,z3,z60,z7,z5,z6,z10]),(0,[z1,z531,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z532,z6]),(0,[z29,z1,z2,z3,z7,z5,z30]),(0,[z533,z1,z2,z3,z7,z5,z6])],[],[(0,[z1,z2,z47,z3,z7,z5,z6]),(0,[z86,z0,z2,z3,z7,z5,z6]),(0,[z86,z1,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z7,z7,z11,z6]),(0,[z150,z1,z2,z3,z7,z5,z69])],[(0,[z1,z534,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z535,z7,z5,z6]),(1,[z103,z2,z3,z7,z5,z10]),(0,[z37,z1,z2,z3,z7,z5,z10]),(0,[z1,z2,z3,z7,z536,z5,z6]),(0,[z1,z2,z3,z133,z7,z374,z6])],[(0,[z537,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z139,z179,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z538,z6]),(0,[z1,z2,z3,z7,z17,z6,z10]),(0,[z150,z1,z2,z417,z7,z5,z6])],[(0,[z1,z2,z3,z7,z539,z5,z6]),(0,[z37,z2,z3,z111,z7,z5,z6]),(0,[z376,z37,z2,z3,z7,z5,z6]),(0,[z1,z2,z90,z3,z7,z11,z6]),(0,[z1,z34,z2,z3,z7,z5,z65]),(0,[z1,z2,z3,z7,z5,z213,z6]),(0,[z1,z2,z3,z7,z17,z96,z6]),(1,[z1,z2,z3,z7,z374,z6])],[(0,[z134,z2,z3,z179,z7,z5,z6]),(0,[z540,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z541,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z542,z5,z6]),(0,[z1,z2,z3,z543,z7,z5,z6]),(1,[z68,z2,z3,z7,z5,z6]),(0,[z150,z1,z23,z3,z7,z5,z6])]],
   [[(0,[z544,z1,z2,z3,z7,z5,z6]),(1,[z1,z140,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z11,z33,z6])],[(0,[z1,z446,z2,z109,z7,z5,z6]),(0,[z1,z2,z3,z111,z7,z229,z6]),(0,[z166,z1,z2,z3,z7,z135,z6]),(0,[z2,z3,z240,z7,z5,z6,z10]),(0,[z1,z545,z2,z3,z7,z5,z6])],[(0,[z546,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z547,z5,z6]),(0,[z2,z3,z7,z5,z33,z6,z523])],[(0,[z71,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z7,z5,z158]),(0,[z37,z2,z3,z133,z7,z5,z6]),(0,[z216,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z7,z232,z6])],[(0,[z2,z3,z7,z441,z5,z6,z10]),(0,[z37,z2,z520,z3,z7,z5,z6]),(0,[z37,z2,z3,z67,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z548,z6])],[(0,[z1,z2,z3,z7,z17,z167,z6]),(0,[z1,z2,z3,z7,z5,z549,z6]),(0,[z391,z37,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z550,z6]),(0,[z1,z2,z54,z7,z5,z6,z30]),(0,[z1,z551,z2,z3,z7,z5,z6]),(0,[z361,z1,z2,z3,z7,z5,z6])],[(0,[z86,z2,z3,z7,z5,z6,z10]),(0,[z37,z2,z3,z7,z5,z141,z6]),(0,[z1,z2,z3,z7,z53,z5,z6]),(0,[z1,z2,z3,z7,z5,z552,z6]),(0,[z1,z2,z553,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z366,z6]),(1,[z2,z3,z7,z5,z6,z523])],[(0,[z554,z1,z2,z3,z7,z5,z6]),(0,[z37,z163,z2,z3,z7,z5,z6]),(0,[z134,z1,z32,z3,z7,z5,z6]),(0,[z555,z1,z2,z3,z7,z5,z6]),(0,[z72,z1,z2,z3,z7,z17,z6]),(0,[z1,z2,z3,z7,z17,z6,z30]),(0,[z1,z2,z3,z7,z5,z33,z6])]],
   [[(0,[z1,z2,z3,z7,z5,z556,z6]),(0,[z1,z2,z3,z557,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z558,z6]),(0,[z1,z2,z3,z7,z5,z158,z6]),(0,[z37,z2,z9,z3,z7,z5,z6]),(0,[z1,z2,z3,z559,z7,z5,z6]),(0,[z1,z211,z2,z139,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z560]),(0,[z1,z2,z3,z561,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z237,z6])],[(0,[z1,z2,z3,z562,z7,z5,z6]),(1,[z216,z2,z3,z7,z5,z6]),(0,[z1,z563,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z564,z5,z6]),(0,[z1,z2,z3,z7,z5,z565,z6]),(0,[z1,z2,z3,z7,z566,z5,z6]),(0,[z567,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z7,z5,z181,z6,z30]),(0,[z1,z2,z3,z7,z5,z6,z568]),(0,[z308,z1,z2,z3,z7,z5,z6])],[(0,[z37,z32,z2,z3,z7,z5,z6]),(0,[z58,z1,z2,z179,z7,z5,z6]),(0,[z128,z1,z2,z3,z7,z5,z6]),(0,[z72,z37,z2,z3,z7,z5,z6]),(0,[z37,z2,z3,z7,z36,z5,z6]),(0,[z569,z1,z2,z3,z7,z5,z6]),(0,[z1,z3,z240,z7,z487,z5,z6]),(1,[z306,z2,z3,z7,z5,z6]),(0,[z25,z1,z2,z390,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z6,z570]),(0,[z1,z2,z3,z7,z61,z17,z6]),(0,[z28,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z240,z7,z5,z6]),(0,[z1,z2,z571,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z21,z11,z6]),(0,[z1,z2,z3,z7,z572,z5,z6]),(0,[z25,z1,z2,z3,z7,z5,z16])],[(0,[z1,z2,z3,z7,z5,z6,z573]),(0,[z72,z1,z2,z9,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z574]),(0,[z1,z2,z240,z7,z36,z5,z6]),(0,[z1,z2,z3,z575,z7,z5,z6])]],
   [[(0,[z1,z2,z3,z7,z5,z576,z6]),(0,[z577,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z578,z6]),(0,[z0,z1,z2,z3,z60,z5,z6]),(0,[z1,z2,z3,z7,z5,z579,z6]),(0,[z1,z2,z3,z7,z580,z5,z6]),(0,[z31,z1,z2,z3,z7,z5,z6]),(0,[z25,z1,z2,z3,z7,z5,z40])],[(0,[z1,z2,z3,z7,z581,z5,z6]),(1,[z1,z2,z390,z7,z5,z6]),(0,[z582,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z133,z7,z5,z16])],[(0,[z583,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z584,z7,z5,z6]),(0,[z1,z2,z47,z3,z7,z11,z6]),(0,[z1,z2,z585,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z586,z5,z6]),(0,[z103,z1,z2,z3,z7,z5,z10]),(1,[z2,z3,z7,z17,z6,z10]),(0,[z1,z2,z3,z7,z587,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z365]),(0,[z1,z2,z3,z7,z17,z6,z16])],[(0,[z163,z1,z2,z3,z7,z17,z6]),(0,[z86,z1,z332,z3,z7,z5,z6]),(0,[z2,z3,z7,z5,z6,z10,z22]),(0,[z150,z1,z2,z3,z7,z17,z6]),(0,[z1,z2,z3,z133,z7,z5,z40])],[(0,[z1,z2,z3,z588,z7,z5,z6]),(0,[z80,z1,z2,z3,z7,z5,z6]),(0,[z62,z1,z2,z3,z7,z441,z6]),(0,[z1,z2,z3,z7,z96,z5,z33])],[(0,[z1,z2,z3,z7,z5,z589,z6]),(0,[z590,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z111,z7,z97,z6]),(0,[z1,z35,z2,z3,z7,z17,z6]),(0,[z1,z2,z3,z7,z17,z65,z6]),(0,[z591,z1,z2,z3,z7,z5,z6])],[(1,[z163,z109,z3,z7,z5,z6]),(1,[z1,z446,z2,z7,z5,z6]),(0,[z2,z3,z7,z586,z5,z6,z10])],[(1,[z1,z2,z7,z5,z6,z217])]],
   [[(0,[z592,z1,z2,z3,z7,z5,z6]),(0,[z150,z37,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z593,z6])],[(0,[z84,z1,z2,z3,z7,z5,z6]),(0,[z86,z2,z3,z7,z135,z5,z6]),(0,[z1,z2,z594,z3,z7,z5,z6]),(1,[z1,z2,z3,z240,z11,z6])],[(0,[z71,z1,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z7,z5,z595,z6]),(0,[z37,z2,z3,z7,z5,z167,z6]),(0,[z1,z2,z3,z7,z596,z5,z6])],[(0,[z597,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z67,z7,z457,z5,z6]),(0,[z598,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z133,z5,z11,z6]),(0,[z188,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z17,z104,z6]),(0,[z1,z2,z3,z7,z17,z6,z105]),(0,[z1,z2,z3,z7,z17,z6,z69]),(0,[z1,z2,z3,z599,z7,z5,z6])],[(0,[z86,z1,z357,z3,z7,z5,z6]),(0,[z37,z2,z3,z7,z5,z6,z30]),(0,[z1,z2,z3,z7,z5,z600,z6]),(0,[z1,z2,z3,z67,z5,z11,z6])],[(0,[z1,z2,z3,z601,z7,z5,z6]),(0,[z269,z1,z211,z2,z7,z5,z6]),(0,[z1,z2,z602,z3,z7,z5,z6])],[(0,[z603,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z7,z321,z6]),(0,[z166,z1,z2,z3,z7,z167,z6]),(0,[z37,z2,z3,z7,z564,z5,z6]),(1,[z1,z2,z417,z7,z5,z6])],[(0,[z1,z2,z3,z7,z604,z5,z6]),(0,[z1,z2,z7,z5,z449,z21,z6]),(0,[z1,z2,z9,z139,z7,z5,z6])]],
   [[(0,[z1,z1,z2,z3,z7,z5,z6]),(0,[z32,z2,z3,z7,z5,z6,z10]),(0,[z1,z2,z3,z7,z605,z5,z6]),(0,[z1,z3,z7,z5,z579,z181,z6]),(0,[z1,z2,z241,z3,z7,z5,z6]),(1,[z1,z23,z3,z7,z5,z6])],[(0,[z1,z2,z3,z606,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z607,z6]),(0,[z2,z3,z7,z5,z6,z194,z10]),(0,[z1,z2,z3,z7,z5,z608,z6]),(0,[z1,z2,z3,z7,z609,z5,z6])],[(1,[z1,z2,z3,z7,z320,z6]),(1,[z1,z2,z3,z7,z5,z125]),(0,[z1,z211,z2,z3,z7,z17,z6]),(0,[z27,z1,z2,z3,z7,z17,z6]),(0,[z1,z610,z2,z3,z7,z5,z6]),(0,[z1,z2,z611,z3,z7,z5,z6]),(0,[z1,z612,z2,z3,z7,z5,z6])],[(0,[z1,z2,z613,z3,z7,z5,z6])],[(0,[z1,z2,z47,z139,z7,z5,z6]),(0,[z148,z1,z2,z3,z7,z5,z6]),(0,[z546,z2,z3,z7,z5,z6,z10]),(0,[z1,z2,z3,z7,z5,z40,z10]),(0,[z12,z1,z2,z3,z61,z5,z6]),(0,[z614,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z240,z7,z11,z6]),(0,[z1,z2,z3,z7,z5,z6,z615]),(0,[z1,z2,z3,z7,z5,z616,z6])],[(0,[z71,z2,z3,z7,z5,z6,z10]),(0,[z2,z3,z7,z135,z5,z6,z10]),(0,[z62,z1,z90,z3,z7,z5,z6]),(0,[z1,z35,z3,z7,z441,z5,z6])],[(0,[z1,z2,z617,z3,z7,z5,z6]),(0,[z2,z3,z7,z5,z6,z10,z280]),(0,[z618,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z619]),(0,[z29,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z620]),(0,[z1,z2,z3,z7,z7,z17,z6])],[(0,[z27,z37,z2,z3,z7,z5,z6]),(0,[z37,z2,z54,z3,z7,z5,z6]),(0,[z37,z2,z3,z7,z5,z6,z16]),(0,[z1,z2,z139,z3,z7,z5,z6]),(0,[z1,z2,z3,z621,z7,z5,z6])]],
   [[(1,[z1,z2,z439,z7,z5,z6]),(0,[z0,z1,z2,z3,z111,z5,z6]),(0,[z166,z264,z2,z3,z7,z5,z6]),(0,[z264,z1,z2,z3,z7,z135,z6]),(0,[z264,z2,z3,z7,z135,z5,z6]),(0,[z2,z3,z7,z5,z6,z10,z464]),(0,[z2,z3,z7,z5,z6,z10,z289]),(0,[z1,z2,z3,z622,z7,z5,z6]),(0,[z1,z2,z54,z7,z94,z5,z6])],[(0,[z77,z2,z3,z7,z5,z6,z10]),(0,[z1,z2,z3,z623,z7,z5,z6]),(0,[z1,z2,z9,z7,z5,z181,z6]),(0,[z1,z624,z2,z3,z7,z5,z6])],[(0,[z62,z72,z1,z3,z7,z5,z6]),(0,[z1,z211,z2,z9,z7,z5,z6]),(0,[z150,z625,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z626])],[(0,[z1,z2,z3,z7,z5,z627,z6]),(0,[z37,z2,z3,z7,z5,z40,z6]),(1,[z1,z2,z7,z457,z5,z6]),(0,[z150,z1,z2,z3,z7,z11,z6]),(0,[z1,z2,z432,z3,z7,z5,z6])],[(0,[z628,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z629,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z630,z6]),(0,[z211,z2,z3,z7,z5,z6,z10]),(0,[z492,z37,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z631,z6]),(0,[z27,z1,z2,z3,z7,z5,z22]),(0,[z1,z2,z3,z632,z7,z5,z6]),(0,[z1,z2,z3,z7,z130,z5,z6])],[(0,[z633,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z634,z3,z7,z5,z6]),(0,[z1,z2,z3,z111,z7,z17,z6]),(0,[z2,z3,z7,z135,z5,z167,z6]),(0,[z2,z3,z7,z5,z167,z6,z10]),(0,[z1,z635,z2,z3,z7,z5,z6]),(0,[z1,z35,z2,z3,z7,z11,z6]),(1,[z2,z3,z7,z5,z6,z83]),(0,[z636,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z637,z6])],[(0,[z638,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z639,z7,z5,z6]),(0,[z1,z34,z3,z7,z5,z65,z6]),(0,[z1,z2,z3,z7,z640,z5,z6]),(0,[z641,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z60,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z642])],[(0,[z1,z2,z3,z7,z643,z5,z6]),(0,[z1,z2,z644,z3,z7,z5,z6]),(0,[z1,z2,z3,z645,z7,z5,z6]),(0,[z1,z2,z3,z7,z646,z5,z6]),(0,[z269,z1,z2,z3,z180,z5,z6])]],
   [[(0,[z647,z1,z2,z3,z7,z5,z6]),(0,[z37,z2,z3,z7,z5,z6,z69]),(0,[z1,z2,z3,z7,z5,z648,z6]),(0,[z25,z1,z2,z3,z7,z5,z6])],[(0,[z71,z134,z2,z3,z7,z5,z6]),(0,[z114,z1,z2,z3,z7,z5,z6]),(1,[z359,z2,z3,z7,z5,z6])],[(0,[z134,z1,z109,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z649,z5,z6]),(0,[z37,z1,z2,z3,z7,z17,z6]),(0,[z112,z1,z2,z3,z7,z5,z6]),(0,[z650,z1,z2,z3,z7,z5,z6]),(0,[z269,z1,z2,z3,z196,z5,z6]),(0,[z598,z1,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z133,z7,z17,z6])],[(0,[z1,z2,z651,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z652,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z405]),(1,[z1,z2,z3,z61,z11,z6]),(0,[z1,z2,z3,z67,z7,z17,z6]),(0,[z1,z2,z653,z3,z7,z5,z6]),(0,[z522,z1,z2,z3,z7,z17,z6])],[(0,[z654,z1,z2,z3,z7,z5,z6]),(0,[z2,z3,z133,z7,z5,z6,z10]),(0,[z1,z2,z3,z7,z441,z11,z6]),(1,[z1,z2,z3,z7,z17,z6])],[(1,[z1,z2,z3,z7,z5,z6]),(0,[z1,z466,z2,z3,z7,z11,z6])],[(0,[z1,z2,z655,z3,z7,z5,z6]),(0,[z656,z1,z2,z3,z7,z5,z6]),(0,[z1,z32,z38,z3,z7,z5,z6]),(0,[z58,z1,z2,z3,z7,z5,z6]),(0,[z150,z2,z3,z7,z5,z6,z10]),(0,[z1,z2,z3,z7,z5,z6,z657]),(0,[z1,z90,z3,z7,z61,z5,z6]),(0,[z1,z2,z658,z3,z7,z5,z6]),(0,[z1,z625,z2,z3,z7,z5,z6])],[(0,[z37,z37,z2,z3,z7,z5,z6]),(0,[z12,z1,z38,z3,z7,z5,z6]),(1,[z1,z3,z7,z5,z579,z6]),(0,[z1,z2,z3,z7,z11,z6,z659])]],
   [[(0,[z208,z1,z3,z179,z7,z5,z6]),(0,[z1,z35,z2,z3,z7,z21,z6]),(0,[z1,z2,z3,z7,z17,z441,z6]),(0,[z660,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z240,z5,z11,z6]),(0,[z1,z2,z9,z3,z7,z17,z6])],[(0,[z661,z1,z2,z3,z7,z5,z6]),(1,[z37,z2,z3,z7,z5,z6]),(1,[z2,z3,z7,z5,z40,z10]),(1,[z1,z2,z3,z7,z381,z6]),(0,[z662,z1,z2,z3,z7,z5,z6]),(1,[z1,z3,z7,z5,z6,z365]),(0,[z1,z663,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z664])],[(0,[z37,z2,z139,z3,z7,z5,z6]),(0,[z1,z211,z2,z3,z7,z11,z6]),(0,[z27,z1,z2,z3,z7,z11,z6]),(0,[z665,z1,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z11,z6,z10]),(0,[z1,z2,z3,z60,z67,z5,z6]),(0,[z666,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z667,z7,z5,z6]),(0,[z31,z1,z2,z3,z5,z11,z6]),(1,[z150,z1,z2,z3,z7,z69]),(0,[z1,z2,z3,z7,z5,z668,z6])],[(0,[z1,z32,z2,z3,z7,z5,z6]),(0,[z1,z2,z669,z3,z7,z5,z6]),(0,[z1,z32,z3,z7,z61,z5,z6]),(0,[z1,z2,z670,z3,z7,z5,z6]),(0,[z527,z37,z2,z3,z7,z5,z6]),(1,[z1,z38,z3,z67,z5,z6]),(0,[z1,z2,z3,z7,z36,z5,z6])],[(0,[z1,z2,z47,z3,z7,z17,z6]),(0,[z1,z2,z332,z3,z7,z5,z6]),(0,[z1,z671,z2,z3,z7,z5,z6]),(0,[z12,z1,z2,z3,z7,z5,z6]),(0,[z12,z1,z3,z7,z61,z5,z6]),(0,[z1,z2,z3,z7,z672,z5,z6]),(0,[z1,z2,z3,z7,z17,z6,z22]),(0,[z29,z1,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z5,z11,z6,z16]),(1,[z106,z2,z3,z7,z5,z6])],[(0,[z673,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z659]),(0,[z674,z1,z2,z3,z7,z5,z6])],[(0,[z675,z1,z2,z3,z7,z5,z6]),(0,[z676,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z239,z5,z6]),(0,[z1,z3,z7,z61,z5,z6,z22]),(0,[z1,z2,z3,z7,z5,z449,z6])]],
   [[(0,[z677,z1,z2,z3,z7,z5,z6]),(0,[z37,z2,z3,z7,z17,z5,z6]),(0,[z1,z2,z3,z7,z5,z678,z6]),(0,[z29,z306,z2,z3,z7,z5,z6])],[(0,[z134,z1,z90,z3,z7,z5,z6]),(0,[z37,z2,z3,z639,z7,z5,z6]),(0,[z37,z2,z3,z60,z7,z5,z6]),(0,[z1,z38,z2,z3,z7,z5,z6]),(0,[z1,z140,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z17,z242,z6]),(0,[z25,z1,z612,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z679])],[(0,[z680,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z10]),(1,[z62,z1,z3,z7,z21,z6]),(0,[z681,z1,z2,z3,z7,z5,z6]),(1,[z31,z1,z2,z3,z11,z6]),(0,[z1,z2,z3,z7,z5,z6,z682]),(0,[z2,z3,z7,z5,z40,z6,z143])],[(0,[z1,z2,z3,z683,z7,z5,z6]),(0,[z2,z90,z3,z7,z5,z6,z10]),(0,[z62,z1,z35,z3,z7,z5,z6]),(0,[z74,z1,z2,z3,z7,z5,z6]),(0,[z684,z1,z2,z3,z7,z5,z6])],[(0,[z1,z685,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z686,z6]),(0,[z1,z2,z7,z94,z5,z181,z6]),(0,[z687,z1,z2,z3,z7,z5,z6]),(0,[z68,z1,z2,z3,z7,z11,z6])],[(0,[z1,z2,z3,z7,z5,z688,z6]),(1,[z134,z32,z3,z7,z5,z6]),(0,[z71,z1,z2,z3,z7,z17,z6]),(0,[z1,z2,z3,z111,z7,z11,z6]),(0,[z264,z1,z2,z3,z7,z167,z6]),(0,[z27,z2,z3,z7,z5,z6,z10]),(1,[z37,z2,z3,z7,z5,z10]),(0,[z1,z90,z3,z7,z441,z5,z6]),(0,[z1,z2,z3,z7,z5,z689,z6]),(0,[z1,z2,z3,z690,z7,z5,z6]),(0,[z1,z2,z3,z7,z11,z6,z30])],[(0,[z134,z72,z1,z3,z7,z5,z6]),(1,[z1,z211,z90,z7,z5,z6]),(0,[z1,z3,z7,z441,z5,z21,z6]),(0,[z1,z3,z7,z5,z65,z6,z22]),(0,[z1,z2,z3,z7,z364,z5,z6]),(0,[z691,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z17,z5,z11,z6]),(1,[z1,z612,z3,z7,z5,z6])],[(0,[z86,z166,z2,z3,z7,z5,z6]),(0,[z114,z2,z3,z7,z5,z141,z6]),(0,[z25,z1,z2,z3,z7,z11,z6]),(0,[z251,z1,z2,z3,z7,z5,z6])]],
   [[(0,[z692,z1,z2,z3,z7,z5,z6]),(0,[z1,z693,z2,z3,z7,z5,z6]),(0,[z103,z1,z2,z3,z7,z17,z6]),(0,[z72,z322,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z7,z13,z6])],[(0,[z1,z2,z164,z3,z7,z5,z6]),(0,[z103,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z455]),(0,[z37,z2,z3,z7,z5,z6,z6]),(0,[z1,z2,z3,z7,z5,z6,z694]),(0,[z1,z2,z3,z7,z17,z263,z6])],[(0,[z71,z37,z2,z3,z7,z5,z6]),(0,[z37,z0,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z167,z6]),(0,[z37,z1,z2,z3,z7,z11,z6]),(0,[z12,z1,z2,z3,z67,z5,z6]),(0,[z1,z2,z3,z133,z7,z11,z6])],[(0,[z273,z1,z2,z3,z7,z5,z6]),(1,[z1,z2,z3,z7,z229,z6]),(0,[z1,z695,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z135,z5,z79,z6]),(0,[z696,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z67,z7,z11,z6]),(0,[z1,z2,z3,z7,z697,z5,z6]),(0,[z698,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z9,z7,z5,z141,z6]),(1,[z625,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z6,z699]),(0,[z700,z1,z2,z3,z7,z5,z6]),(0,[z62,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z6,z30]),(1,[z1,z2,z3,z7,z11,z6])],[(0,[z58,z1,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z7,z701,z5,z6]),(0,[z103,z37,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z702,z5,z6]),(1,[z1,z3,z7,z487,z5,z6]),(0,[z1,z2,z3,z7,z566,z17,z6]),(0,[z1,z703,z2,z3,z7,z5,z6])],[(0,[z1,z38,z109,z3,z7,z5,z6]),(0,[z1,z38,z2,z3,z67,z5,z6]),(0,[z704,z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z33,z6,z69])],[(0,[z1,z2,z3,z7,z705,z5,z6]),(0,[z1,z2,z706,z3,z7,z5,z6]),(0,[z1,z2,z3,z240,z7,z17,z6]),(0,[z1,z2,z571,z3,z7,z17,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z2,z9,z7,z5,z141,z10]),(0,[z37,z707,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z708]),(0,[z2,z3,z7,z5,z267,z10]),(0,[z25,z192,z2,z3,z5,z16])],[(1,[z2,z709,z7,z5,z6]),(0,[z2,z709,z179,z7,z5,z6]),(0,[z1,z2,z3,z11,z6,z480]),(0,[z1,z2,z7,z457,z5,z6]),(0,[z1,z2,z3,z118,z318,z6]),(0,[z710,z1,z3,z7,z17,z6])],[(0,[z590,z1,z2,z3,z11,z6]),(0,[z2,z3,z7,z5,z6,z711])],[(0,[z2,z3,z7,z5,z6,z83]),(0,[z166,z2,z3,z7,z167,z6]),(0,[z1,z2,z3,z7,z712,z6])],[(0,[z108,z2,z179,z7,z5,z6]),(0,[z89,z2,z3,z5,z10,z16])],[(0,[z1,z2,z174,z7,z5,z6]),(0,[z1,z3,z7,z5,z713,z6]),(0,[z37,z2,z714,z7,z5,z6]),(0,[z37,z2,z139,z240,z5,z6]),(0,[z1,z2,z3,z61,z13,z6]),(0,[z74,z1,z2,z715,z5,z6]),(0,[z1,z3,z7,z716,z5,z6]),(0,[z717,z2,z3,z7,z11,z6])],[(0,[z1,z90,z3,z53,z5,z6]),(0,[z2,z3,z7,z5,z6,z718]),(0,[z1,z2,z3,z7,z5,z719]),(0,[z1,z2,z54,z7,z580,z6])],[(0,[z37,z720,z2,z7,z5,z6]),(0,[z721,z2,z3,z7,z5,z6]),(0,[z722,z2,z3,z7,z5,z6])],[(0,[z2,z3,z5,z194,z10,z16]),(0,[z1,z3,z7,z11,z723,z6])],[(0,[z163,z322,z3,z7,z5,z6]),(0,[z108,z1,z7,z61,z5,z6]),(0,[z2,z3,z5,z79,z6,z10]),(0,[z37,z2,z3,z7,z724,z6]),(0,[z1,z2,z3,z421,z11,z6]),(0,[z1,z2,z3,z291,z96,z6])],[(0,[z2,z3,z5,z6,z10,z725])],[(0,[z1,z2,z3,z7,z726,z6]),(0,[z148,z2,z3,z398,z5,z6]),(0,[z492,z37,z2,z3,z11,z6]),(0,[z72,z1,z3,z53,z5,z6]),(0,[z727,z2,z3,z7,z5,z6])],[(0,[z1,z728,z3,z7,z5,z6])],[(0,[z1,z2,z3,z729,z11,z6])],[(0,[z2,z3,z7,z5,z694,z10]),(0,[z269,z436,z1,z7,z5,z6])]],
   [[(0,[z37,z2,z3,z7,z5,z6]),(0,[z1,z2,z730,z7,z5,z6]),(0,[z1,z2,z3,z7,z11,z125]),(0,[z37,z731,z3,z7,z5,z6]),(0,[z1,z3,z7,z5,z723,z6]),(0,[z1,z2,z9,z7,z17,z141])],[(0,[z208,z1,z3,z7,z5,z6]),(0,[z2,z7,z5,z6,z10,z217]),(0,[z1,z2,z3,z7,z732,z6])],[(0,[z58,z2,z709,z7,z5,z6]),(0,[z1,z2,z54,z7,z733,z6]),(0,[z150,z1,z2,z3,z7,z105]),(0,[z150,z1,z2,z3,z7,z69])],[(0,[z734,z1,z2,z3,z7,z6]),(0,[z1,z2,z3,z735,z5,z6])],[(0,[z106,z2,z3,z7,z5,z6]),(0,[z736,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z737,z6]),(0,[z1,z2,z3,z7,z738,z6]),(0,[z1,z2,z3,z7,z739,z6]),(0,[z1,z437,z3,z67,z5,z6])],[(0,[z555,z1,z2,z3,z11,z6]),(0,[z86,z1,z332,z3,z11,z6]),(0,[z1,z2,z3,z512,z17,z6]),(0,[z103,z2,z3,z7,z17,z10]),(0,[z2,z3,z7,z373,z6,z10]),(0,[z1,z2,z3,z7,z740,z6]),(0,[z1,z2,z741,z7,z5,z6])],[(0,[z1,z90,z584,z7,z5,z6]),(0,[z1,z2,z439,z7,z11,z6]),(0,[z1,z2,z3,z7,z6,z742])],[(0,[z37,z38,z3,z67,z5,z6]),(0,[z743,z2,z3,z7,z5,z6]),(0,[z68,z2,z3,z61,z11,z6]),(0,[z1,z2,z139,z715,z5,z6]),(0,[z1,z2,z3,z744,z5,z6])],[(0,[z31,z1,z2,z3,z745,z6]),(0,[z68,z2,z3,z7,z17,z6])],[(0,[z62,z1,z3,z7,z21,z6]),(0,[z269,z1,z2,z180,z181,z6])],[(0,[z746,z2,z3,z7,z5,z6])],[(0,[z1,z2,z747,z7,z5,z6]),(0,[z748,z1,z2,z7,z5,z6]),(0,[z2,z3,z7,z5,z338,z10]),(0,[z677,z1,z2,z3,z11,z6]),(0,[z2,z3,z7,z321,z6,z10]),(0,[z37,z2,z3,z7,z17,z10]),(0,[z1,z749,z3,z7,z5,z6])],[(0,[z2,z3,z7,z318,z6,z10]),(0,[z2,z3,z133,z5,z40,z10]),(0,[z27,z212,z3,z7,z5,z22]),(0,[z76,z1,z2,z3,z11,z6]),(0,[z1,z2,z3,z7,z96,z750])],[(0,[z258,z1,z3,z7,z5,z22])],[(0,[z1,z90,z7,z596,z5,z6]),(0,[z1,z241,z3,z7,z5,z6]),(0,[z1,z2,z553,z3,z11,z6]),(0,[z1,z2,z390,z7,z130,z6])],[(0,[z1,z2,z3,z7,z751,z6]),(0,[z1,z2,z3,z7,z13,z6]),(0,[z1,z2,z3,z7,z752,z6])]],
   [[(0,[z0,z2,z3,z111,z97,z6]),(0,[z1,z2,z3,z7,z5,z753])],[(0,[z37,z211,z90,z7,z5,z6]),(0,[z1,z2,z3,z7,z754,z6]),(0,[z1,z2,z3,z7,z755,z6])],[(0,[z276,z1,z2,z3,z11,z6]),(0,[z625,z2,z3,z7,z5,z6]),(0,[z2,z3,z7,z5,z199,z10]),(0,[z1,z2,z3,z5,z756,z6]),(0,[z1,z3,z7,z5,z757,z22]),(0,[z1,z2,z3,z7,z758,z6]),(0,[z1,z2,z3,z7,z745,z6])],[(0,[z446,z2,z7,z5,z6,z10]),(0,[z37,z2,z3,z7,z13,z6]),(0,[z1,z2,z3,z759,z5,z6])],[(0,[z2,z760,z3,z7,z5,z6]),(0,[z761,z2,z3,z7,z5,z6]),(0,[z1,z2,z571,z7,z94,z6]),(0,[z1,z2,z3,z242,z11,z6])],[(0,[z1,z2,z7,z17,z449,z6]),(0,[z306,z2,z3,z7,z17,z6]),(0,[z1,z2,z762,z7,z11,z6])],[(0,[z37,z2,z3,z7,z229,z6])],[(0,[z763,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z764,z6]),(1,[z1,z2,z3,z7,z750])],[(0,[z1,z2,z3,z7,z5,z765]),(0,[z766,z2,z3,z7,z5,z10]),(0,[z37,z3,z7,z487,z5,z6]),(0,[z1,z767,z3,z7,z5,z6]),(0,[z29,z1,z2,z7,z17,z30])],[(0,[z768,z2,z3,z7,z5,z6])],[(0,[z37,z2,z3,z7,z5,z402]),(0,[z2,z3,z5,z11,z10,z16])],[(0,[z1,z2,z3,z5,z769,z6]),(0,[z770,z1,z3,z7,z5,z6]),(0,[z492,z2,z3,z7,z5,z10]),(0,[z771,z2,z3,z7,z5,z6]),(0,[z1,z772,z3,z7,z17,z6])],[(0,[z1,z2,z3,z773,z5,z6]),(0,[z12,z3,z61,z5,z6,z10]),(0,[z774,z2,z3,z7,z17,z6])],[(0,[z1,z2,z3,z7,z5,z775]),(0,[z113,z1,z3,z7,z21,z6])],[(0,[z1,z2,z7,z776,z5,z6]),(0,[z777,z2,z3,z7,z5,z6]),(0,[z1,z778,z3,z7,z5,z6])],[(0,[z779,z1,z3,z7,z5,z6])]],
   [[(0,[z1,z2,z7,z5,z733,z6]),(0,[z1,z2,z3,z416,z11,z6])],[(0,[z150,z37,z2,z3,z7,z69]),(0,[z1,z2,z3,z7,z11,z780])],[(0,[z72,z1,z623,z7,z5,z6]),(0,[z1,z2,z781,z7,z5,z6]),(0,[z1,z231,z3,z7,z373,z6]),(0,[z782,z1,z2,z7,z11,z6])],[(0,[z2,z3,z133,z11,z6,z10]),(0,[z37,z2,z3,z7,z11,z10]),(0,[z1,z2,z7,z94,z565,z6]),(0,[z1,z2,z3,z7,z783,z6])],[(0,[z37,z446,z2,z7,z5,z6]),(0,[z37,z2,z3,z67,z11,z6]),(0,[z1,z612,z3,z7,z11,z6]),(0,[z25,z1,z2,z3,z17,z16])],[(0,[z784,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z313,z17,z6])],[(0,[z1,z2,z3,z7,z785,z6]),(0,[z344,z1,z3,z7,z242,z6]),(0,[z1,z2,z85,z7,z17,z6])],[(0,[z546,z2,z179,z7,z5,z6]),(0,[z1,z2,z417,z7,z17,z6])],[(0,[z62,z37,z3,z7,z21,z6]),(0,[z72,z1,z645,z7,z5,z6]),(0,[z114,z2,z3,z7,z17,z6])],[(0,[z2,z390,z7,z5,z6,z10]),(0,[z37,z2,z3,z7,z96,z33]),(0,[z1,z2,z3,z786,z5,z6]),(0,[z74,z1,z2,z36,z5,z6]),(0,[z2,z3,z7,z5,z6,z787]),(0,[z2,z3,z7,z11,z6,z143])],[(0,[z208,z1,z139,z7,z5,z6]),(0,[z37,z2,z3,z7,z97,z6]),(0,[z27,z28,z3,z7,z5,z22]),(0,[z119,z1,z2,z3,z11,z6]),(0,[z110,z68,z2,z3,z11,z6]),(0,[z2,z3,z7,z5,z788,z6])],[],[(0,[z1,z2,z3,z355,z17,z6]),(0,[z1,z231,z3,z7,z232,z6]),(0,[z1,z2,z390,z7,z237,z6])],[(0,[z171,z1,z2,z3,z11,z6]),(0,[z2,z3,z7,z11,z10,z16]),(0,[z114,z3,z7,z5,z6,z365]),(0,[z1,z241,z390,z7,z5,z6])],[(0,[z37,z23,z3,z7,z5,z6]),(0,[z1,z2,z9,z7,z5,z608]),(0,[z789,z1,z2,z7,z11,z6])],[(0,[z2,z3,z339,z5,z6,z10]),(0,[z790,z3,z7,z5,z6,z10]),(0,[z1,z211,z7,z421,z5,z6])]],
   [[(0,[z2,z3,z7,z5,z6,z143]),(0,[z1,z791,z169,z7,z5,z6]),(0,[z29,z1,z2,z7,z11,z30]),(0,[z1,z2,z3,z256,z5,z6]),(0,[z1,z2,z432,z256,z5,z6])],[(0,[z1,z2,z439,z7,z17,z6]),(0,[z792,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z130,z6]),(0,[z68,z2,z3,z11,z6,z16]),(0,[z2,z3,z7,z17,z6,z793])],[],[(0,[z2,z3,z7,z5,z10,z57]),(0,[z2,z3,z7,z5,z10,z16]),(0,[z157,z1,z2,z3,z11,z6])],[(0,[z37,z2,z3,z7,z5,z352]),(0,[z1,z2,z3,z53,z11,z6])],[(0,[z37,z2,z3,z7,z130,z6]),(0,[z1,z2,z3,z794,z5,z6]),(0,[z2,z3,z7,z5,z6,z795])],[(0,[z1,z164,z3,z7,z5,z6])],[(0,[z1,z2,z3,z230,z11,z6]),(0,[z1,z2,z3,z60,z373,z6]),(0,[z1,z612,z85,z7,z5,z6]),(0,[z150,z1,z2,z3,z256,z69])],[(0,[z1,z2,z3,z7,z796,z6]),(0,[z211,z90,z7,z5,z6,z10]),(0,[z37,z2,z7,z457,z5,z6]),(0,[z797,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z798,z6]),(0,[z106,z2,z3,z7,z130,z6])],[(0,[z37,z2,z3,z7,z712,z6]),(0,[z1,z2,z799,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z750])],[(0,[z72,z1,z683,z7,z5,z6]),(0,[z1,z332,z3,z7,z5,z158]),(0,[z80,z2,z51,z7,z5,z6]),(0,[z1,z2,z60,z457,z5,z6]),(0,[z269,z1,z2,z7,z18,z6]),(0,[z25,z1,z2,z3,z11,z16])],[(0,[z37,z2,z174,z7,z5,z6]),(0,[z2,z7,z5,z6,z10,z800]),(0,[z1,z2,z3,z572,z11,z6])],[(0,[z2,z3,z111,z5,z79,z6]),(0,[z68,z2,z3,z7,z135,z6]),(0,[z1,z2,z85,z7,z11,z6])],[(0,[z1,z2,z801,z7,z5,z6]),(0,[z492,z2,z3,z7,z5,z125]),(0,[z0,z2,z3,z111,z229,z6]),(0,[z1,z2,z417,z7,z11,z6])]],
   [[(0,[z136,z72,z1,z7,z5,z6]),(0,[z1,z2,z3,z11,z6,z176]),(0,[z1,z2,z3,z581,z11,z6]),(0,[z114,z2,z3,z7,z11,z6]),(0,[z625,z23,z3,z7,z5,z6])],[(0,[z1,z2,z179,z36,z11,z6]),(0,[z1,z2,z802,z7,z5,z6]),(0,[z1,z2,z3,z587,z11,z6]),(0,[z308,z2,z432,z7,z5,z6])],[(0,[z28,z2,z3,z7,z11,z6])],[(0,[z0,z2,z3,z7,z5,z125]),(0,[z1,z2,z803,z7,z5,z6])],[(0,[z71,z322,z2,z7,z5,z6]),(0,[z72,z1,z557,z7,z5,z6]),(0,[z1,z2,z3,z66,z11,z6]),(0,[z216,z2,z337,z7,z5,z6]),(0,[z1,z2,z3,z7,z804,z6])],[(0,[z1,z805,z3,z7,z5,z6]),(0,[z1,z357,z3,z7,z5,z158]),(0,[z1,z2,z3,z196,z297,z6])],[(0,[z2,z3,z7,z5,z10,z619]),(0,[z1,z806,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z807])],[(0,[z1,z808,z3,z7,z5,z6]),(0,[z2,z3,z7,z5,z323,z10]),(0,[z74,z37,z2,z36,z5,z6]),(0,[z809,z2,z3,z7,z5,z6]),(0,[z1,z2,z810,z7,z11,z6])],[(0,[z1,z2,z811,z7,z5,z6]),(0,[z1,z2,z3,z596,z11,z6]),(0,[z2,z3,z7,z11,z6,z812])],[],[(0,[z37,z2,z3,z7,z5,z404]),(0,[z2,z3,z7,z813,z5,z6]),(0,[z1,z2,z266,z7,z5,z6]),(0,[z1,z3,z191,z61,z5,z6]),(0,[z674,z1,z2,z3,z11,z6])],[(0,[z1,z2,z3,z7,z239,z6]),(0,[z1,z814,z3,z7,z5,z6])],[(0,[z166,z2,z3,z7,z104,z6]),(0,[z161,z2,z3,z7,z167,z6]),(0,[z1,z2,z3,z87,z11,z6]),(0,[z1,z2,z3,z7,z815,z6]),(0,[z1,z2,z3,z196,z5,z6]),(0,[z1,z2,z240,z715,z5,z6])],[(0,[z1,z2,z3,z7,z816,z6]),(0,[z817,z1,z2,z7,z5,z6]),(0,[z1,z35,z3,z7,z348,z6]),(0,[z1,z2,z288,z7,z377,z6])],[(0,[z666,z1,z2,z7,z5,z30]),(0,[z1,z612,z3,z7,z17,z6])]],
   [[(0,[z1,z2,z818,z7,z5,z6]),(0,[z1,z2,z7,z5,z6,z819]),(0,[z1,z2,z3,z7,z237,z6]),(0,[z2,z3,z7,z5,z6,z812])],[(0,[z72,z1,z59,z7,z5,z6]),(0,[z1,z2,z7,z5,z6,z820])],[(0,[z37,z749,z3,z7,z5,z6]),(0,[z821,z1,z3,z7,z11,z6])],[(0,[z2,z3,z7,z398,z5,z10]),(0,[z1,z2,z3,z177,z11,z6])],[(0,[z134,z322,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z822]),(0,[z37,z2,z3,z7,z237,z6]),(0,[z1,z231,z139,z240,z5,z6]),(0,[z1,z2,z823,z7,z17,z6])],[(0,[z37,z241,z3,z7,z5,z6]),(0,[z1,z2,z7,z11,z824,z6])],[],[(0,[z212,z2,z3,z7,z5,z6]),(0,[z1,z332,z3,z7,z321,z6]),(0,[z2,z3,z7,z5,z362,z10]),(0,[z2,z3,z7,z381,z6,z10])],[(0,[z1,z2,z825,z7,z5,z6]),(0,[z37,z2,z3,z7,z5,z262]),(0,[z826,z1,z2,z3,z7,z6]),(0,[z1,z2,z3,z827,z5,z6]),(0,[z106,z2,z3,z7,z237,z6])],[(0,[z1,z3,z7,z5,z828,z6]),(0,[z37,z2,z3,z5,z756,z6]),(0,[z829,z2,z3,z7,z5,z6]),(0,[z106,z241,z3,z7,z5,z6])],[(0,[z1,z2,z3,z830,z5,z6])],[(0,[z1,z332,z3,z7,z320,z6]),(0,[z1,z332,z3,z7,z5,z125])],[(0,[z1,z2,z831,z7,z5,z6]),(0,[z1,z2,z7,z5,z824,z6])],[(0,[z317,z2,z3,z7,z5,z10])],[(0,[z103,z2,z3,z7,z5,z775]),(0,[z1,z231,z3,z7,z5,z6]),(0,[z1,z3,z60,z487,z5,z6]),(0,[z832,z1,z2,z7,z5,z6]),(0,[z1,z23,z3,z256,z5,z6])],[(0,[z833,z2,z3,z7,z11,z6])]],
   [[(0,[z37,z208,z3,z7,z5,z6]),(0,[z1,z834,z3,z7,z5,z6]),(0,[z1,z357,z3,z7,z321,z6]),(0,[z12,z1,z3,z61,z5,z6]),(0,[z1,z2,z3,z53,z17,z6])],[(0,[z1,z332,z439,z7,z5,z6]),(0,[z2,z3,z7,z135,z320,z6]),(0,[z2,z3,z7,z135,z5,z125]),(0,[z1,z835,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z836])],[(0,[z1,z837,z3,z7,z5,z6]),(0,[z1,z2,z709,z7,z5,z6]),(0,[z838,z2,z3,z7,z5,z6])],[(0,[z839,z1,z3,z7,z5,z6]),(0,[z1,z2,z3,z429,z11,z6]),(0,[z840,z2,z3,z7,z5,z6]),(0,[z841,z1,z3,z7,z5,z6]),(0,[z2,z3,z7,z5,z6,z842])],[(0,[z163,z108,z1,z7,z5,z6]),(0,[z1,z2,z7,z843,z5,z6]),(0,[z1,z357,z3,z7,z320,z6]),(0,[z1,z357,z3,z7,z5,z125]),(0,[z2,z3,z7,z5,z10,z244]),(0,[z37,z2,z3,z7,z5,z775]),(0,[z844,z2,z3,z7,z5,z6])],[(0,[z2,z3,z7,z4,z5,z125]),(0,[z1,z2,z845,z7,z5,z6]),(0,[z279,z1,z2,z3,z11,z6])],[(0,[z2,z7,z5,z449,z6,z10]),(0,[z2,z337,z7,z5,z6,z10]),(0,[z1,z2,z3,z7,z846,z6]),(0,[z27,z1,z3,z7,z17,z22]),(0,[z847,z2,z3,z7,z5,z6])],[(1,[z1,z332,z3,z11,z6]),(0,[z1,z2,z3,z7,z848,z6]),(0,[z849,z2,z3,z7,z5,z6]),(0,[z188,z1,z2,z3,z5,z16]),(0,[z850,z1,z3,z7,z5,z6]),(0,[z2,z3,z7,z851,z197,z6])],[(0,[z1,z2,z3,z852,z5,z6]),(0,[z27,z3,z7,z5,z10,z22]),(0,[z2,z432,z7,z5,z6,z10]),(0,[z391,z520,z3,z7,z5,z6]),(0,[z1,z38,z3,z204,z5,z6]),(0,[z1,z2,z3,z7,z318,z6]),(0,[z68,z2,z3,z7,z56,z6])],[(0,[z1,z2,z853,z7,z5,z6]),(0,[z2,z3,z5,z854,z6,z10]),(0,[z37,z2,z845,z7,z5,z6]),(0,[z1,z3,z487,z5,z11,z6])],[(0,[z1,z357,z439,z7,z5,z6]),(0,[z1,z2,z855,z7,z5,z6]),(0,[z2,z3,z7,z56,z11,z6]),(0,[z192,z2,z3,z7,z11,z6])],[(0,[z208,z58,z1,z7,z5,z6]),(0,[z1,z2,z3,z73,z11,z6]),(0,[z1,z209,z3,z7,z5,z6]),(0,[z1,z209,z432,z7,z5,z6])],[(0,[z1,z2,z3,z7,z6,z856]),(0,[z1,z2,z332,z3,z11,z6]),(0,[z2,z3,z7,z5,z10,z699]),(0,[z1,z2,z3,z291,z5,z6]),(0,[z1,z2,z432,z291,z5,z6])],[(0,[z1,z332,z3,z7,z17,z6]),(0,[z86,z2,z3,z4,z5,z158]),(0,[z527,z2,z292,z7,z5,z6]),(0,[z28,z2,z3,z7,z17,z6]),(0,[z1,z857,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z858]),(0,[z1,z2,z337,z7,z17,z6])],[(0,[z2,z3,z7,z5,z414,z10]),(0,[z1,z859,z3,z7,z5,z6]),(0,[z2,z3,z7,z6,z10,z856]),(0,[z860,z3,z7,z5,z6,z10]),(0,[z1,z38,z3,z67,z318,z6]),(0,[z1,z3,z7,z861,z21,z6]),(0,[z308,z23,z3,z7,z5,z6])]],
   [[(0,[z1,z2,z3,z862,z5,z6]),(0,[z1,z2,z3,z339,z321,z6]),(0,[z2,z3,z7,z96,z33,z10]),(0,[z91,z1,z2,z7,z17,z6]),(0,[z1,z3,z7,z5,z863,z6])],[(0,[z864,z2,z3,z7,z5,z6]),(0,[z1,z2,z7,z733,z181,z6])],[(0,[z58,z2,z179,z7,z5,z6]),(0,[z1,z2,z3,z865,z5,z6]),(0,[z86,z2,z3,z813,z5,z6]),(0,[z1,z2,z3,z7,z866,z6]),(0,[z1,z2,z9,z36,z11,z6])],[(0,[z1,z2,z3,z5,z79,z6]),(0,[z867,z2,z3,z7,z5,z6]),(0,[z12,z1,z3,z61,z13,z6])],[(0,[z868,z2,z3,z7,z5,z6])],[(0,[z1,z869,z3,z7,z5,z6]),(0,[z612,z3,z7,z5,z6,z10]),(0,[z2,z3,z7,z11,z6,z459]),(0,[z870,z1,z2,z3,z7,z11])],[(0,[z1,z357,z3,z7,z17,z6]),(0,[z2,z3,z7,z5,z6,z775]),(0,[z871,z1,z2,z3,z7,z5])],[(0,[z1,z2,z3,z7,z6,z872]),(0,[z1,z2,z3,z11,z6,z125]),(0,[z37,z2,z3,z5,z79,z6]),(0,[z37,z2,z3,z256,z5,z6]),(0,[z2,z3,z67,z56,z11,z6]),(0,[z361,z2,z3,z7,z17,z6])],[(0,[z434,z2,z3,z7,z5,z10]),(0,[z68,z2,z3,z36,z11,z6]),(0,[z269,z1,z2,z7,z181,z6])],[(0,[z322,z38,z3,z7,z5,z6]),(0,[z873,z2,z3,z7,z5,z6])],[(0,[z72,z1,z791,z7,z5,z6]),(1,[z1,z2,z457,z11,z6]),(0,[z1,z2,z3,z7,z874,z6]),(0,[z875,z2,z3,z7,z5,z6]),(0,[z29,z306,z2,z7,z5,z30]),(0,[z150,z308,z2,z3,z7,z69])],[(0,[z238,z109,z3,z7,z5,z6]),(0,[z876,z1,z2,z7,z5,z6]),(0,[z1,z2,z877,z7,z5,z6]),(0,[z1,z878,z3,z7,z5,z6])],[(0,[z1,z2,z879,z7,z5,z6]),(0,[z2,z3,z7,z5,z6,z459]),(0,[z2,z3,z7,z5,z880,z6]),(0,[z881,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z271,z11,z6]),(0,[z1,z2,z3,z7,z197,z6])],[(0,[z358,z2,z3,z7,z5,z10]),(0,[z37,z2,z3,z794,z5,z6]),(0,[z1,z2,z9,z7,z5,z470])],[(0,[z37,z2,z3,z7,z5,z529]),(0,[z37,z164,z3,z7,z5,z6]),(0,[z322,z2,z3,z7,z17,z6]),(0,[z27,z1,z3,z7,z11,z22]),(0,[z1,z2,z3,z882,z5,z6]),(0,[z68,z2,z3,z133,z11,z6]),(0,[z192,z2,z85,z7,z5,z6])],[(0,[z12,z37,z3,z61,z5,z6])]],
   [[(0,[z330,z109,z3,z7,z5,z6]),(0,[z883,z2,z3,z7,z5,z6])],[(0,[z32,z884,z3,z7,z5,z6]),(0,[z1,z2,z3,z196,z94,z6])],[(0,[z1,z2,z3,z7,z374,z6]),(0,[z2,z3,z7,z11,z6,z885])],[(0,[z1,z2,z886,z7,z5,z6]),(0,[z71,z2,z594,z7,z5,z6]),(0,[z359,z2,z3,z7,z5,z158]),(0,[z86,z1,z2,z3,z11,z158]),(0,[z426,z1,z3,z61,z5,z6])],[(0,[z1,z2,z3,z7,z5,z887]),(0,[z308,z2,z3,z7,z5,z6]),(0,[z72,z1,z334,z7,z5,z6])],[(0,[z1,z332,z3,z7,z11,z6]),(0,[z86,z1,z2,z3,z97,z6]),(0,[z1,z2,z3,z204,z11,z6]),(0,[z1,z2,z3,z7,z888,z6]),(0,[z1,z2,z3,z118,z17,z6]),(0,[z1,z889,z3,z7,z5,z6]),(0,[z1,z2,z3,z482,z11,z6])],[(0,[z1,z3,z61,z11,z6,z22]),(0,[z890,z2,z3,z7,z5,z6]),(0,[z1,z2,z337,z7,z11,z6])],[(0,[z1,z2,z3,z7,z5,z158]),(0,[z2,z3,z7,z5,z483,z10]),(0,[z2,z3,z61,z56,z11,z6]),(0,[z1,z231,z139,z7,z5,z6]),(0,[z1,z241,z3,z7,z130,z6])],[(0,[z108,z1,z2,z7,z17,z6]),(0,[z91,z1,z2,z7,z11,z6]),(0,[z1,z2,z3,z7,z891,z6]),(0,[z1,z892,z3,z7,z11,z6]),(0,[z2,z3,z7,z17,z6,z523])],[(0,[z2,z3,z7,z5,z775,z10]),(0,[z1,z140,z9,z7,z5,z141]),(0,[z2,z3,z7,z5,z6,z885]),(0,[z1,z893,z3,z7,z5,z6]),(0,[z625,z2,z3,z256,z5,z6])],[(0,[z134,z208,z3,z7,z5,z6]),(0,[z37,z2,z3,z7,z5,z578])],[(0,[z894,z2,z3,z7,z5,z6])],[(0,[z86,z2,z3,z4,z320,z6]),(0,[z86,z2,z3,z4,z5,z125]),(0,[z1,z2,z3,z180,z17,z6])],[(0,[z662,z2,z3,z7,z5,z10]),(0,[z1,z2,z3,z7,z895,z6]),(0,[z1,z2,z3,z7,z33,z750])],[(0,[z216,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z896,z6]),(0,[z1,z357,z3,z7,z11,z6])],[(0,[z166,z2,z3,z7,z320,z6]),(0,[z166,z2,z3,z7,z5,z125]),(0,[z1,z2,z3,z11,z81,z16]),(0,[z361,z2,z3,z7,z11,z6])]],
   [[(0,[z897,z1,z2,z3,z5,z6]),(0,[z1,z898,z3,z7,z5,z6])],[(0,[z72,z1,z651,z7,z5,z6]),(0,[z86,z2,z3,z56,z11,z6]),(0,[z1,z2,z3,z7,z899,z6]),(0,[z1,z2,z9,z7,z5,z900]),(0,[z901,z2,z3,z7,z11,z6])],[(0,[z208,z58,z179,z7,z5,z6]),(0,[z86,z2,z439,z4,z5,z6]),(0,[z31,z2,z3,z11,z6,z10]),(0,[z37,z2,z266,z7,z5,z6])],[(0,[z1,z2,z3,z5,z902,z6]),(0,[z1,z2,z3,z7,z903,z6]),(0,[z231,z3,z7,z5,z6,z10]),(0,[z37,z2,z3,z7,z239,z6]),(0,[z112,z2,z3,z7,z17,z6]),(0,[z1,z2,z3,z904,z5,z6]),(0,[z2,z3,z240,z56,z11,z6]),(0,[z1,z2,z3,z240,z905,z6])],[(0,[z37,z2,z3,z7,z5,z570]),(0,[z37,z2,z3,z196,z5,z6]),(0,[z1,z2,z7,z11,z6,z217]),(0,[z1,z2,z3,z123,z11,z6])],[(0,[z1,z2,z3,z7,z906,z6]),(0,[z907,z1,z3,z7,z5,z6]),(0,[z908,z2,z3,z7,z5,z6]),(0,[z1,z38,z266,z67,z5,z6]),(0,[z1,z2,z3,z53,z566,z6]),(0,[z192,z2,z3,z7,z17,z6])],[(0,[z322,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z18,z11,z6])],[(0,[z269,z37,z2,z7,z181,z6]),(0,[z909,z2,z3,z7,z5,z6]),(0,[z910,z2,z3,z7,z17,z6])],[(0,[z911,z2,z3,z7,z11,z6]),(0,[z161,z2,z3,z7,z6,z280]),(0,[z1,z2,z3,z745,z11,z6])],[(0,[z1,z32,z3,z61,z11,z6]),(0,[z91,z1,z7,z5,z6,z22])],[(0,[z1,z23,z3,z291,z5,z6])],[(0,[z1,z2,z7,z5,z6,z217]),(0,[z1,z2,z3,z149,z11,z6])],[(0,[z25,z1,z2,z390,z5,z16])],[(0,[z1,z2,z912,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z913]),(0,[z1,z2,z3,z118,z11,z6]),(0,[z1,z2,z3,z240,z11,z6]),(0,[z150,z1,z2,z3,z7,z750])],[(0,[z1,z2,z3,z7,z5,z914]),(0,[z1,z3,z7,z5,z6,z915]),(0,[z1,z2,z3,z339,z11,z6]),(0,[z2,z7,z457,z5,z6,z10]),(0,[z1,z2,z3,z11,z6,z260])],[(0,[z208,z1,z7,z36,z5,z6]),(0,[z1,z916,z3,z7,z5,z6]),(0,[z1,z2,z3,z17,z11,z6])]],
   [[(0,[z108,z1,z2,z7,z11,z6]),(0,[z2,z3,z291,z5,z6,z10]),(0,[z1,z2,z7,z5,z362,z30]),(0,[z150,z1,z23,z3,z7,z69])],[(0,[z1,z2,z7,z457,z318,z6])],[(0,[z1,z2,z3,z917,z5,z6]),(0,[z86,z1,z2,z3,z11,z125]),(0,[z1,z211,z791,z7,z5,z6])],[(0,[z2,z3,z5,z56,z79,z6]),(0,[z918,z2,z3,z7,z6,z10]),(0,[z37,z2,z831,z7,z5,z6]),(0,[z1,z2,z3,z7,z919,z6])],[(0,[z2,z3,z7,z920,z6,z10]),(0,[z1,z2,z3,z180,z11,z6])],[(0,[z921,z2,z3,z7,z5,z6]),(0,[z37,z231,z3,z7,z5,z6]),(0,[z922,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z923,z6]),(0,[z1,z2,z3,z7,z366,z33]),(0,[z1,z241,z3,z7,z237,z6]),(0,[z924,z2,z3,z7,z197,z6])],[(0,[z1,z2,z3,z7,z925,z6]),(0,[z1,z2,z3,z7,z320,z6]),(0,[z1,z2,z3,z7,z5,z125]),(0,[z926,z1,z3,z7,z5,z6]),(0,[z2,z3,z5,z6,z10,z927])],[(0,[z1,z2,z3,z7,z928,z6]),(0,[z192,z612,z3,z7,z5,z6])],[(0,[z2,z3,z7,z239,z6,z10])],[(0,[z2,z3,z7,z229,z6,z10]),(0,[z37,z837,z3,z7,z5,z6])],[(0,[z1,z2,z929,z7,z5,z6]),(0,[z2,z3,z7,z5,z549,z10]),(0,[z2,z3,z175,z5,z6,z194]),(0,[z150,z1,z2,z3,z291,z69])],[(0,[z2,z3,z11,z6,z194,z10]),(0,[z112,z2,z3,z7,z11,z6])],[(0,[z1,z2,z3,z7,z5,z930]),(0,[z1,z2,z3,z931,z5,z6]),(0,[z269,z1,z2,z7,z733,z6])],[(0,[z932,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z933,z5,z6]),(0,[z2,z3,z7,z5,z851,z6])],[(0,[z2,z3,z7,z5,z158,z10]),(0,[z86,z68,z2,z3,z11,z6]),(0,[z72,z1,z7,z370,z5,z6]),(0,[z2,z3,z7,z11,z6,z934]),(0,[z1,z2,z3,z133,z237,z6])],[(0,[z62,z3,z7,z21,z6,z10]),(0,[z2,z3,z7,z364,z6,z10]),(0,[z37,z2,z3,z7,z318,z6]),(0,[z2,z3,z7,z17,z6,z83])]],
   [[(0,[z1,z2,z3,z935,z11,z6]),(0,[z1,z2,z3,z7,z936,z6]),(0,[z445,z2,z3,z7,z17,z6]),(0,[z710,z1,z3,z7,z5,z6])],[(0,[z1,z2,z3,z222,z11,z6]),(0,[z2,z3,z7,z5,z6,z937])],[(0,[z2,z3,z7,z5,z125,z10]),(0,[z86,z2,z3,z135,z11,z6]),(0,[z37,z209,z3,z7,z5,z6]),(0,[z37,z2,z3,z7,z11,z81]),(0,[z1,z2,z266,z67,z11,z6])],[(0,[z37,z2,z3,z291,z5,z6]),(0,[z1,z2,z3,z7,z938,z6])],[(0,[z37,z2,z3,z7,z5,z500]),(0,[z1,z939,z2,z7,z5,z6]),(0,[z2,z3,z196,z5,z6,z10]),(0,[z907,z37,z3,z7,z5,z6]),(0,[z1,z2,z940,z7,z5,z6]),(0,[z1,z2,z54,z7,z377,z6])],[(0,[z1,z2,z7,z5,z941,z6]),(0,[z1,z2,z942,z7,z5,z6]),(0,[z2,z3,z7,z5,z6,z934])],[(0,[z86,z2,z3,z4,z11,z6]),(0,[z1,z2,z3,z159,z11,z6])],[(0,[z943,z2,z3,z7,z11,z6])],[(0,[z1,z3,z7,z944,z5,z6]),(0,[z1,z90,z791,z7,z5,z6]),(0,[z62,z1,z3,z7,z242,z6]),(0,[z436,z1,z3,z7,z17,z6]),(0,[z1,z2,z432,z7,z17,z6])],[],[(0,[z2,z3,z7,z97,z6,z10]),(0,[z945,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z946,z6])],[(0,[z1,z2,z3,z947,z5,z6]),(0,[z1,z2,z3,z427,z11,z6]),(0,[z2,z439,z7,z5,z6,z10]),(0,[z1,z2,z3,z7,z948,z6]),(0,[z1,z2,z762,z7,z5,z6])],[(0,[z166,z1,z2,z3,z79,z6]),(0,[z949,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z950,z6]),(0,[z2,z3,z7,z6,z10,z872]),(0,[z1,z2,z3,z951,z5,z6]),(0,[z1,z2,z3,z7,z381,z6]),(0,[z684,z1,z2,z3,z11,z6])],[(0,[z884,z2,z3,z7,z5,z6]),(0,[z134,z108,z1,z7,z5,z6]),(0,[z1,z2,z3,z265,z11,z6]),(0,[z150,z2,z3,z7,z10,z69]),(0,[z1,z90,z7,z5,z415,z6]),(0,[z1,z2,z3,z7,z952,z6]),(0,[z426,z1,z3,z7,z21,z6]),(0,[z1,z2,z9,z7,z5,z141])],[(0,[z1,z2,z3,z7,z953,z6]),(0,[z954,z2,z3,z7,z5,z6]),(0,[z1,z3,z7,z579,z11,z6]),(0,[z1,z955,z3,z7,z5,z6])]],
   [[(1,[z1,z2,z7,z733,z6]),(0,[z436,z1,z9,z7,z5,z6])],[(0,[z1,z2,z3,z272,z11,z6]),(0,[z2,z3,z7,z5,z600,z10]),(0,[z2,z3,z60,z5,z10,z16]),(0,[z359,z2,z3,z7,z5,z10]),(0,[z1,z2,z3,z7,z96,z263])],[(0,[z2,z3,z7,z5,z6,z956])],[(0,[z1,z2,z957,z7,z5,z6]),(0,[z103,z2,z3,z7,z5,z10]),(0,[z37,z2,z3,z7,z197,z6]),(0,[z1,z3,z7,z5,z958,z6]),(0,[z1,z959,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z960]),(0,[z1,z109,z3,z61,z11,z6]),(0,[z2,z174,z7,z5,z6,z10]),(0,[z1,z2,z174,z7,z5,z158]),(0,[z1,z38,z3,z67,z381,z6]),(0,[z598,z1,z2,z36,z5,z6]),(0,[z625,z209,z3,z7,z5,z6])],[(0,[z625,z2,z3,z291,z5,z6])],[(0,[z68,z2,z3,z7,z5,z6]),(0,[z1,z3,z7,z933,z5,z6]),(0,[z1,z2,z3,z7,z905,z6]),(0,[z1,z139,z240,z487,z5,z6]),(0,[z1,z2,z139,z240,z11,z6]),(0,[z1,z140,z3,z7,z17,z6]),(0,[z31,z1,z2,z3,z11,z6])],[(0,[z1,z2,z3,z7,z961,z6])],[(0,[z1,z2,z3,z7,z962,z6]),(0,[z782,z1,z2,z7,z5,z6]),(0,[z1,z2,z3,z7,z963,z6]),(0,[z445,z2,z3,z7,z11,z6])],[(0,[z1,z2,z3,z339,z17,z6]),(0,[z1,z964,z3,z7,z5,z6]),(0,[z37,z2,z3,z7,z5,z10]),(0,[z37,z2,z3,z7,z374,z6]),(0,[z72,z1,z169,z7,z11,z6]),(0,[z965,z2,z3,z7,z5,z6]),(0,[z25,z1,z612,z3,z5,z16])],[(0,[z1,z34,z3,z7,z5,z95])],[(0,[z884,z109,z3,z7,z5,z6]),(0,[z86,z2,z3,z4,z321,z6]),(0,[z1,z2,z3,z7,z966,z6]),(0,[z1,z2,z3,z967,z5,z6])],[(0,[z71,z2,z51,z7,z5,z6]),(0,[z1,z2,z7,z5,z968,z6])],[(0,[z2,z802,z7,z5,z6,z10]),(0,[z1,z790,z3,z7,z5,z6]),(0,[z1,z2,z73,z36,z5,z6]),(0,[z1,z2,z3,z60,z745,z6])],[(0,[z1,z2,z7,z5,z6,z969]),(0,[z37,z2,z3,z7,z5,z158]),(0,[z29,z2,z7,z5,z10,z30]),(0,[z1,z2,z3,z7,z970,z6]),(0,[z1,z140,z9,z7,z5,z6])],[(0,[z1,z2,z3,z7,z971,z6]),(0,[z1,z2,z3,z240,z213,z6])]],
   [[(0,[z436,z1,z3,z7,z11,z6]),(0,[z1,z2,z432,z7,z11,z6]),(0,[z1,z2,z7,z5,z6,z972])],[(0,[z973,z1,z3,z7,z5,z6]),(0,[z1,z2,z3,z321,z11,z6]),(0,[z1,z2,z3,z5,z11,z125]),(0,[z974,z2,z3,z7,z5,z6]),(0,[z62,z1,z3,z7,z861,z6]),(0,[z975,z2,z3,z7,z5,z6])],[(0,[z37,z91,z2,z7,z5,z6]),(0,[z1,z2,z3,z318,z11,z6]),(0,[z1,z2,z3,z905,z11,z6]),(0,[z1,z2,z976,z7,z17,z6])],[(0,[z306,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z79,z11,z6]),(0,[z1,z3,z67,z933,z5,z6])],[(1,[z2,z3,z813,z5,z6]),(0,[z977,z1,z2,z7,z5,z6]),(0,[z1,z2,z3,z17,z686,z6]),(0,[z29,z1,z2,z7,z5,z900]),(0,[z789,z1,z2,z7,z5,z6])],[(0,[z1,z34,z3,z61,z11,z6]),(0,[z978,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z979,z6]),(0,[z29,z1,z2,z7,z5,z30]),(0,[z3,z7,z5,z6,z459,z365])],[(0,[z1,z2,z439,z5,z11,z6]),(0,[z37,z0,z2,z3,z11,z6]),(0,[z980,z2,z3,z5,z6,z10]),(0,[z981,z2,z3,z7,z5,z6]),(0,[z1,z2,z390,z7,z17,z6])],[(0,[z89,z2,z3,z11,z6,z10]),(0,[z2,z3,z7,z5,z6,z982]),(0,[z269,z1,z7,z579,z181,z6])],[(0,[z86,z1,z2,z439,z11,z6]),(0,[z2,z3,z7,z5,z6,z983]),(0,[z1,z2,z3,z67,z13,z6]),(0,[z984,z2,z3,z7,z5,z6]),(0,[z1,z772,z3,z7,z5,z6]),(0,[z985,z1,z3,z7,z5,z6])],[(0,[z1,z2,z3,z346,z11,z6]),(0,[z1,z2,z986,z7,z5,z6]),(0,[z774,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z987,z6])],[(0,[z1,z2,z3,z7,z5,z988]),(0,[z163,z109,z3,z7,z17,z6]),(0,[z1,z2,z3,z5,z6,z725]),(0,[z77,z3,z7,z5,z168,z6]),(0,[z37,z2,z3,z7,z906,z6])],[(0,[z1,z989,z3,z7,z5,z6]),(0,[z2,z3,z7,z5,z131,z10]),(0,[z37,z2,z3,z7,z17,z81]),(0,[z1,z2,z471,z240,z5,z6])],[(0,[z990,z2,z3,z7,z5,z6]),(0,[z1,z140,z3,z7,z11,z6])],[(0,[z717,z2,z3,z7,z5,z6]),(0,[z1,z2,z7,z5,z141,z900])]],
   [[(0,[z163,z108,z109,z7,z5,z6])],[(0,[z86,z2,z3,z4,z17,z6]),(0,[z0,z2,z3,z813,z5,z6]),(0,[z2,z3,z7,z991,z6,z10]),(0,[z72,z1,z7,z496,z5,z6])],[(0,[z2,z3,z7,z213,z6,z10]),(0,[z37,z2,z7,z5,z6,z217]),(0,[z1,z2,z3,z11,z6,z431]),(0,[z1,z2,z3,z11,z6,z433]),(0,[z25,z1,z2,z3,z5,z16])],[(0,[z1,z2,z174,z7,z320,z6]),(0,[z1,z2,z174,z7,z5,z125]),(0,[z188,z1,z2,z3,z7,z659])],[(0,[z37,z2,z3,z240,z11,z6]),(0,[z1,z2,z85,z7,z5,z6]),(0,[z2,z3,z17,z56,z11,z6]),(0,[z992,z2,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z321,z6]),(0,[z2,z85,z7,z5,z6,z10]),(0,[z31,z37,z2,z3,z11,z6]),(0,[z1,z2,z417,z7,z5,z6])],[(0,[z1,z2,z3,z993,z5,z6]),(0,[z114,z2,z3,z7,z5,z6]),(0,[z1,z2,z994,z7,z5,z6]),(0,[z37,z2,z3,z17,z11,z6]),(0,[z1,z2,z3,z995,z5,z6]),(0,[z1,z2,z3,z7,z861,z6]),(0,[z1,z2,z54,z7,z94,z6])],[(0,[z72,z1,z2,z196,z5,z6]),(0,[z2,z3,z36,z56,z11,z6])],[(0,[z2,z3,z7,z5,z6,z996]),(0,[z997,z2,z3,z7,z5,z6]),(0,[z998,z2,z3,z7,z5,z6])],[(0,[z1,z612,z390,z7,z5,z6])],[(0,[z68,z2,z3,z67,z11,z6])],[(0,[z1,z2,z3,z17,z79,z6]),(1,[z1,z3,z933,z5,z6]),(0,[z2,z3,z7,z17,z6,z143])],[(0,[z1,z2,z999,z7,z5,z6]),(0,[z2,z3,z5,z40,z10,z16]),(0,[z1,z2,z7,z11,z6,z1000])],[(0,[z37,z2,z3,z7,z320,z6]),(0,[z37,z2,z3,z7,z5,z125]),(0,[z1,z2,z3,z392,z11,z6]),(0,[z1,z2,z3,z1001,z5,z6])],[(0,[z2,z3,z7,z5,z10,z424]),(0,[z110,z1,z2,z3,z11,z6]),(0,[z1002,z2,z3,z7,z5,z6]),(0,[z1,z1003,z3,z7,z5,z6])],[(0,[z1,z2,z1004,z7,z5,z6]),(0,[z1,z2,z439,z7,z5,z6]),(0,[z2,z3,z7,z17,z10,z16]),(0,[z1,z2,z390,z7,z11,z6])]],
   [[(0,[z58,z164,z179,z7,z5,z6]),(0,[z1005,z2,z3,z7,z5,z6]),(0,[z25,z106,z2,z3,z5,z16])],[(0,[z2,z3,z61,z11,z6,z10]),(0,[z37,z2,z929,z7,z5,z6]),(0,[z91,z1,z7,z441,z5,z6]),(0,[z1,z2,z139,z240,z17,z6]),(0,[z1006,z2,z3,z7,z5,z6]),(0,[z1007,z2,z3,z7,z5,z6])],[(0,[z140,z3,z7,z5,z6,z459]),(0,[z1,z3,z7,z5,z6,z1008])],[(0,[z37,z2,z439,z7,z5,z6]),(0,[z12,z1,z3,z61,z239,z6])],[(0,[z163,z109,z3,z7,z11,z6]),(0,[z1,z446,z2,z7,z11,z6]),(0,[z2,z3,z7,z705,z5,z10]),(0,[z0,z1,z2,z3,z97,z6]),(0,[z72,z1,z169,z7,z17,z6]),(0,[z114,z140,z3,z7,z5,z6])],[(1,[z884,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z1009,z6])],[(0,[z163,z520,z3,z7,z5,z6]),(0,[z1,z2,z7,z457,z381,z6])],[(0,[z359,z2,z3,z7,z17,z6])],[(0,[z876,z2,z7,z5,z6,z10]),(0,[z1,z2,z7,z449,z11,z6]),(0,[z1,z1010,z3,z7,z5,z6]),(0,[z2,z3,z1011,z7,z11,z6])],[(0,[z583,z1,z2,z3,z11,z6]),(1,[z2,z3,z11,z10,z16]),(0,[z2,z3,z7,z11,z40,z10]),(0,[z1,z2,z3,z1012,z5,z6]),(0,[z1,z3,z7,z11,z6,z365])],[(0,[z1,z2,z3,z61,z11,z6]),(0,[z1,z2,z266,z7,z318,z6]),(0,[z1013,z2,z3,z7,z5,z6]),(0,[z1014,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z472,z11,z6]),(0,[z25,z1,z2,z85,z5,z16])],[(0,[z1,z2,z3,z7,z17,z6]),(0,[z1,z2,z47,z36,z11,z6]),(0,[z308,z2,z3,z256,z5,z6])],[(0,[z1,z2,z3,z7,z1015,z6]),(0,[z1,z231,z7,z36,z5,z6]),(0,[z1,z2,z3,z1016,z5,z6]),(0,[z1,z2,z3,z599,z17,z6]),(0,[z1,z2,z1017,z7,z5,z6])],[(0,[z1,z2,z7,z1018,z5,z6])],[(0,[z2,z3,z7,z5,z6,z1019]),(0,[z2,z3,z7,z197,z6,z10]),(0,[z1,z3,z7,z5,z579,z6]),(0,[z62,z91,z1,z7,z5,z6]),(0,[z2,z3,z7,z5,z6,z1020]),(1,[z1,z2,z7,z5,z900]),(0,[z1,z23,z3,z7,z11,z6]),(0,[z1,z2,z1021,z7,z5,z6]),(0,[z150,z625,z2,z3,z7,z69])],[(0,[z1,z2,z3,z7,z1022,z6]),(0,[z1,z2,z3,z7,z6,z750])]],
   [[(0,[z0,z2,z3,z56,z11,z6]),(0,[z2,z3,z7,z5,z40,z10]),(0,[z1,z2,z3,z7,z1023,z6]),(0,[z1,z3,z7,z5,z6,z365]),(0,[z2,z3,z7,z5,z6,z1024])],[(0,[z1,z2,z3,z7,z1025,z6]),(0,[z1,z2,z3,z7,z1026,z6]),(0,[z25,z37,z2,z3,z5,z16]),(0,[z1,z2,z1027,z7,z5,z6])],[(0,[z88,z2,z3,z7,z5,z10]),(0,[z1,z1028,z3,z7,z5,z6]),(0,[z72,z1,z559,z7,z5,z6]),(0,[z1,z38,z3,z67,z17,z6]),(0,[z1,z2,z3,z1029,z5,z6])],[(0,[z583,z1,z3,z61,z5,z6]),(0,[z1030,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z750,z69])],[(0,[z134,z107,z3,z7,z5,z6]),(0,[z1,z2,z3,z343,z11,z6]),(1,[z1,z2,z3,z11,z125]),(0,[z2,z3,z7,z5,z99,z10]),(0,[z37,z2,z3,z7,z381,z6])],[(0,[z108,z322,z2,z7,z5,z6]),(0,[z37,z2,z9,z7,z5,z141]),(0,[z1031,z2,z3,z7,z5,z6]),(0,[z1032,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z1033,z6]),(0,[z833,z2,z3,z7,z5,z6]),(0,[z188,z1,z2,z3,z7,z69]),(0,[z25,z1,z2,z3,z5,z1034])],[(0,[z134,z301,z3,z7,z5,z6]),(0,[z331,z1,z3,z61,z5,z6]),(0,[z1,z2,z3,z457,z11,z6]),(0,[z1,z2,z3,z291,z202,z6])],[(0,[z71,z2,z709,z7,z5,z6]),(0,[z1,z34,z337,z7,z5,z6]),(0,[z1035,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z1036,z6])],[(0,[z1,z2,z1037,z7,z5,z6]),(0,[z1,z2,z3,z5,z1034,z16])],[(0,[z1,z2,z7,z457,z11,z6]),(0,[z1,z2,z3,z7,z1038,z6]),(0,[z1,z2,z3,z7,z733,z6])],[(0,[z1,z2,z1039,z7,z5,z6]),(0,[z1,z2,z3,z606,z11,z6]),(0,[z1,z2,z3,z7,z1040,z6]),(0,[z1,z2,z3,z7,z5,z780])],[(0,[z134,z32,z3,z7,z17,z6]),(0,[z1,z2,z1041,z7,z5,z6]),(0,[z1,z1042,z3,z7,z5,z6])],[(0,[z86,z1,z357,z3,z11,z6]),(0,[z89,z1,z2,z3,z11,z6]),(0,[z1,z211,z90,z7,z17,z6]),(0,[z1,z2,z3,z667,z11,z6])],[(0,[z1,z612,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z1043,z6])],[(0,[z1,z1044,z3,z7,z5,z6]),(0,[z248,z2,z3,z7,z5,z10]),(0,[z74,z2,z36,z5,z6,z10]),(0,[z1,z2,z3,z373,z11,z6]),(0,[z1,z2,z3,z180,z373,z6]),(0,[z1,z2,z3,z7,z1045,z6]),(0,[z1,z2,z3,z7,z11,z719]),(0,[z110,z2,z3,z7,z104,z6])],[(0,[z1,z2,z3,z479,z11,z6]),(0,[z2,z3,z813,z4,z5,z6]),(0,[z1,z2,z3,z7,z935,z6]),(0,[z1,z1046,z3,z7,z5,z6]),(0,[z2,z266,z7,z5,z6,z10]),(0,[z1,z211,z2,z196,z5,z6]),(0,[z359,z2,z3,z7,z11,z6])]],
   [[(0,[z2,z3,z7,z232,z6,z10])],[(0,[z86,z332,z3,z4,z5,z6])],[(0,[z1,z2,z3,z7,z1047,z6]),(0,[z1,z1048,z3,z7,z5,z6]),(0,[z1,z2,z1049,z7,z5,z6]),(0,[z1,z3,z7,z5,z6,z757]),(0,[z1,z2,z3,z487,z11,z6]),(0,[z1,z2,z3,z17,z225,z6]),(0,[z1,z2,z823,z7,z5,z6]),(0,[z1050,z1,z2,z7,z5,z6])],[(0,[z1,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z7,z1051,z6]),(0,[z1,z3,z7,z487,z17,z6]),(0,[z1,z23,z417,z7,z5,z6])],[],[(0,[z1,z1052,z3,z7,z5,z6]),(0,[z1,z2,z3,z93,z11,z6])],[(0,[z1053,z2,z3,z7,z5,z6]),(0,[z1,z3,z7,z5,z6,z1054])],[(0,[z1,z2,z1055,z7,z5,z6]),(0,[z37,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z7,z1056,z6]),(0,[z2,z3,z7,z11,z6,z10]),(0,[z1,z2,z3,z496,z11,z6]),(0,[z1,z2,z3,z7,z1057,z6]),(0,[z1,z1058,z3,z7,z5,z6]),(0,[z1,z2,z3,z291,z6,z69])],[(0,[z2,z3,z111,z5,z6,z194]),(0,[z1,z2,z9,z7,z5,z548])],[(0,[z1,z2,z3,z7,z5,z1059]),(0,[z166,z2,z3,z7,z162,z6]),(0,[z1,z2,z3,z7,z729,z6])],[(0,[z1,z2,z7,z5,z6,z800]),(0,[z86,z357,z3,z4,z5,z6]),(0,[z2,z3,z7,z5,z183,z10]),(0,[z1,z211,z7,z5,z532,z6]),(0,[z1,z38,z3,z67,z11,z6])],[(0,[z357,z3,z7,z5,z6,z10]),(0,[z269,z436,z1,z7,z181,z6]),(0,[z106,z2,z3,z7,z11,z6])],[(0,[z2,z709,z3,z7,z5,z6]),(0,[z507,z2,z3,z7,z5,z10])],[(0,[z1,z2,z457,z5,z11,z6]),(0,[z1,z2,z7,z94,z733,z6])],[(0,[z2,z3,z7,z5,z6,z10]),(0,[z1,z2,z3,z1060,z5,z6]),(0,[z1,z2,z3,z53,z5,z6]),(0,[z1061,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z517,z11,z6]),(0,[z1,z209,z3,z291,z5,z6])],[(0,[z1,z446,z2,z7,z17,z6]),(0,[z1,z3,z7,z1062,z5,z6]),(0,[z2,z3,z7,z374,z6,z10]),(0,[z1,z1063,z3,z7,z5,z6]),(0,[z1,z2,z7,z5,z1064,z6]),(0,[z2,z3,z7,z96,z33,z523])]],
   [[(0,[z661,z72,z1,z7,z5,z6]),(0,[z1,z3,z67,z61,z11,z6])],[(0,[z1,z2,z3,z7,z1065,z6]),(0,[z1066,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z552,z11,z6])],[(0,[z1,z2,z174,z7,z321,z6]),(0,[z1067,z2,z3,z7,z5,z6]),(0,[z29,z445,z2,z7,z5,z30]),(0,[z1,z2,z7,z5,z6,z900])],[(0,[z134,z32,z3,z7,z11,z6]),(0,[z1,z2,z3,z1068,z5,z6]),(0,[z1,z2,z3,z11,z6,z41]),(0,[z1,z2,z3,z60,z318,z6])],[(0,[z2,z3,z67,z11,z6,z10]),(0,[z1069,z2,z3,z7,z5,z6]),(0,[z1,z211,z90,z7,z11,z6]),(0,[z2,z3,z7,z5,z6,z1070]),(0,[z27,z1,z3,z7,z5,z22]),(0,[z436,z1,z7,z5,z6,z30])],[(0,[z72,z1,z632,z7,z5,z6]),(0,[z1,z1071,z3,z7,z5,z6]),(0,[z1,z2,z3,z11,z6,z16]),(0,[z1,z209,z3,z256,z5,z6])],[(0,[z72,z169,z7,z5,z6,z10]),(0,[z1,z2,z3,z515,z11,z6]),(0,[z1,z2,z3,z5,z745,z6])],[],[(0,[z269,z1,z2,z7,z220,z6])],[(0,[z625,z2,z3,z7,z11,z6]),(0,[z1,z23,z3,z7,z17,z6])],[(0,[z3,z7,z487,z5,z6,z10])],[(0,[z28,z2,z3,z7,z5,z6]),(0,[z1,z332,z3,z7,z5,z6]),(0,[z37,z2,z85,z7,z5,z6]),(0,[z1,z2,z3,z191,z11,z6]),(0,[z62,z1,z3,z53,z21,z6]),(0,[z1,z3,z7,z487,z11,z6]),(0,[z1,z2,z3,z575,z11,z6])],[(0,[z37,z2,z3,z7,z321,z6]),(0,[z1072,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z920,z6]),(0,[z37,z2,z417,z7,z5,z6]),(0,[z1,z2,z3,z190,z11,z6]),(0,[z1,z2,z337,z7,z5,z6]),(0,[z1,z2,z3,z1073,z5,z6]),(0,[z319,z1,z2,z3,z11,z6])],[(0,[z2,z3,z7,z5,z246,z10]),(0,[z37,z2,z54,z7,z94,z6])],[(0,[z72,z322,z169,z7,z5,z6]),(0,[z91,z1,z2,z7,z5,z6]),(0,[z1074,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z11,z6,z105])],[(0,[z2,z417,z7,z5,z6,z10]),(0,[z192,z2,z390,z7,z5,z6]),(0,[z106,z2,z85,z7,z5,z6])]],
   [[(0,[z71,z2,z47,z7,z17,z6])],[(0,[z2,z3,z256,z5,z6,z10]),(0,[z2,z3,z7,z5,z6,z1075]),(0,[z1,z2,z810,z7,z5,z6]),(0,[z192,z2,z3,z7,z5,z16])],[(0,[z209,z3,z7,z5,z6,z10]),(0,[z1,z140,z7,z5,z6,z30])],[(0,[z1,z3,z7,z5,z6,z1076]),(0,[z2,z3,z7,z5,z56,z6]),(0,[z1,z2,z3,z1077,z5,z6]),(0,[z1078,z2,z3,z7,z5,z6])],[(0,[z1,z357,z3,z7,z5,z6]),(0,[z2,z3,z7,z265,z5,z10]),(0,[z1,z2,z7,z457,z17,z6])],[(0,[z361,z2,z3,z7,z5,z6]),(0,[z2,z3,z7,z880,z11,z6])],[(0,[z37,z2,z1004,z7,z5,z6]),(0,[z1,z2,z3,z7,z1079,z6]),(0,[z1,z1080,z3,z7,z5,z6]),(0,[z1,z2,z3,z488,z11,z6]),(0,[z1,z2,z7,z5,z6,z1000]),(0,[z308,z209,z3,z7,z5,z6])],[(0,[z2,z3,z7,z237,z6,z10]),(0,[z1,z2,z3,z11,z6,z619]),(0,[z1,z2,z3,z561,z11,z6]),(0,[z1,z2,z3,z7,z364,z6]),(0,[z2,z3,z7,z17,z6,z459]),(0,[z1,z1081,z3,z7,z11,z6]),(0,[z308,z2,z3,z291,z5,z6])],[(0,[z1,z2,z3,z7,z5,z1082]),(0,[z1,z2,z3,z5,z1083,z6]),(0,[z1,z2,z174,z7,z17,z6]),(0,[z2,z3,z7,z320,z6,z10]),(0,[z1,z2,z1084,z7,z5,z6]),(0,[z29,z37,z2,z7,z5,z30])],[(0,[z89,z2,z3,z4,z5,z6]),(0,[z2,z3,z56,z79,z11,z6])],[(0,[z2,z3,z7,z56,z97,z6]),(0,[z1,z2,z3,z7,z991,z6]),(0,[z1,z2,z3,z566,z11,z6])],[(0,[z1,z2,z613,z3,z11,z6]),(0,[z821,z1,z3,z7,z5,z6]),(0,[z1,z3,z7,z17,z958,z6])],[(0,[z322,z2,z3,z7,z5,z6]),(0,[z164,z3,z7,z5,z6,z10]),(0,[z322,z3,z7,z61,z5,z6]),(0,[z1,z38,z67,z457,z5,z6]),(0,[z2,z337,z7,z5,z6,z83]),(0,[z1,z2,z3,z256,z374,z6])],[(0,[z1,z2,z3,z7,z1085,z6]),(0,[z2,z47,z709,z7,z5,z6]),(0,[z2,z3,z7,z5,z463,z10]),(0,[z1,z2,z3,z60,z374,z6])],[(0,[z37,z2,z3,z7,z5,z46]),(0,[z86,z2,z3,z11,z6,z10]),(0,[z911,z2,z3,z7,z5,z6]),(0,[z625,z2,z417,z7,z5,z6])],[(0,[z58,z322,z2,z7,z5,z6]),(0,[z1086,z1,z2,z7,z5,z6]),(0,[z1087,z2,z3,z7,z5,z6])]],
   [[(0,[z0,z2,z3,z111,z11,z6]),(0,[z2,z3,z240,z11,z6,z10]),(0,[z1,z2,z3,z53,z21,z6]),(0,[z1,z2,z715,z36,z5,z6])],[(0,[z37,z2,z3,z61,z11,z6]),(0,[z330,z1,z2,z3,z11,z6])],[(0,[z37,z2,z3,z7,z17,z6]),(0,[z2,z3,z7,z5,z1088,z6]),(0,[z1,z3,z7,z5,z556,z22]),(0,[z1,z231,z3,z240,z11,z6])],[(0,[z208,z1,z3,z7,z17,z6]),(0,[z27,z37,z3,z7,z5,z22]),(0,[z1,z2,z3,z118,z5,z6]),(0,[z1,z34,z3,z7,z5,z648]),(0,[z1,z612,z3,z7,z130,z6])],[(0,[z166,z2,z3,z7,z56,z6]),(0,[z3,z7,z5,z6,z10,z915])],[(0,[z37,z3,z7,z5,z579,z6]),(0,[z1,z2,z7,z5,z6,z1089]),(0,[z1,z2,z3,z7,z213,z6]),(0,[z1090,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z237,z6,z16])],[(0,[z108,z1,z2,z7,z5,z6]),(0,[z1,z1091,z3,z7,z5,z6]),(0,[z1,z2,z1092,z7,z5,z6]),(0,[z1,z2,z3,z11,z6,z194]),(0,[z106,z2,z3,z7,z17,z6])],[(0,[z1,z2,z1093,z7,z5,z6]),(0,[z2,z3,z7,z5,z10,z145]),(0,[z25,z2,z3,z5,z10,z16]),(0,[z37,z3,z7,z5,z6,z365]),(0,[z2,z3,z7,z5,z6,z1094]),(0,[z1,z2,z3,z11,z6,z199])],[(0,[z1,z2,z101,z3,z11,z6]),(0,[z71,z2,z47,z7,z11,z6]),(0,[z37,z2,z3,z7,z1026,z6]),(0,[z533,z1,z2,z3,z11,z6])],[(0,[z1,z2,z3,z7,z1095,z6]),(0,[z37,z2,z3,z7,z213,z6]),(0,[z2,z3,z7,z11,z1096,z6])],[(0,[z1,z2,z3,z1097,z5,z6]),(0,[z546,z2,z7,z5,z6,z289]),(0,[z1,z2,z3,z180,z5,z6])],[(0,[z1,z1098,z3,z7,z5,z6])],[(0,[z71,z134,z72,z7,z5,z6])],[(0,[z2,z3,z1099,z5,z6,z10]),(0,[z1,z2,z3,z420,z11,z6])],[(0,[z1,z164,z3,z7,z11,z6]),(0,[z2,z3,z17,z11,z6,z10]),(0,[z2,z3,z7,z1100,z6,z10]),(0,[z1,z2,z3,z604,z11,z6]),(0,[z91,z1,z34,z7,z5,z6])],[(0,[z766,z2,z3,z7,z5,z6]),(0,[z37,z2,z1037,z7,z5,z6]),(0,[z1,z2,z266,z7,z381,z6]),(0,[z269,z1,z2,z196,z181,z6]),(0,[z1,z2,z3,z133,z11,z16]),(0,[z1,z2,z3,z5,z6,z1034])]],
   [[(0,[z675,z1,z2,z36,z5,z6]),(0,[z1,z2,z174,z7,z11,z6]),(0,[z359,z2,z3,z7,z5,z81]),(0,[z1,z2,z3,z7,z1101,z6]),(0,[z2,z3,z7,z5,z1096,z6]),(1,[z1,z3,z487,z11,z6]),(0,[z493,z1,z2,z7,z181,z6]),(0,[z1,z241,z3,z7,z17,z6])],[(0,[z112,z2,z3,z7,z5,z6]),(0,[z86,z166,z2,z3,z11,z6]),(0,[z140,z3,z7,z5,z6,z10]),(0,[z1,z2,z3,z11,z6,z234])],[(0,[z2,z3,z111,z813,z5,z6]),(0,[z1,z211,z7,z5,z6,z516]),(0,[z2,z7,z5,z6,z83,z217]),(0,[z1102,z2,z3,z7,z5,z6])],[(0,[z108,z1,z38,z7,z5,z6]),(0,[z192,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z11,z6,z682])],[(0,[z1,z38,z3,z50,z5,z6]),(0,[z2,z3,z7,z5,z356,z10]),(0,[z37,z612,z3,z7,z5,z6]),(0,[z1,z2,z139,z204,z5,z6]),(0,[z1,z3,z240,z487,z11,z6]),(0,[z625,z2,z3,z7,z17,z6])],[(0,[z1,z2,z3,z7,z5,z1103]),(0,[z1,z2,z3,z1104,z5,z6]),(0,[z1,z2,z1105,z7,z5,z6]),(0,[z910,z2,z3,z7,z5,z6])],[(0,[z1,z332,z3,z5,z11,z6]),(0,[z1,z2,z1106,z7,z5,z6]),(0,[z1107,z2,z3,z7,z5,z6]),(0,[z1,z2,z7,z17,z6,z217]),(0,[z598,z1,z2,z7,z296,z6])],[],[(0,[z1,z2,z1108,z7,z5,z6]),(0,[z106,z612,z3,z7,z5,z6])],[(0,[z1,z2,z67,z457,z11,z6]),(0,[z1,z2,z3,z409,z11,z6]),(1,[z1,z2,z3,z745,z6])],[(0,[z86,z2,z3,z5,z56,z6]),(0,[z1,z2,z7,z5,z449,z6]),(0,[z1,z2,z3,z1109,z5,z6]),(0,[z1110,z2,z3,z7,z5,z6])],[(0,[z208,z1,z3,z7,z11,z6]),(0,[z2,z3,z7,z135,z97,z6]),(0,[z1,z1111,z3,z7,z5,z6]),(0,[z68,z2,z3,z7,z167,z6]),(0,[z25,z1,z2,z3,z130,z16])],[(0,[z1,z2,z417,z256,z5,z6])],[(0,[z1,z2,z3,z60,z321,z6]),(0,[z1,z2,z85,z7,z130,z6])],[(0,[z37,z108,z2,z7,z5,z6]),(0,[z1,z2,z3,z7,z1112,z6]),(0,[z86,z2,z3,z5,z79,z6]),(0,[z1086,z37,z2,z7,z5,z6])],[(0,[z1,z2,z3,z1113,z5,z6])]],
   [[(0,[z208,z109,z3,z7,z5,z6]),(0,[z1114,z2,z3,z7,z5,z6]),(0,[z614,z1,z2,z3,z11,z6])],[(0,[z537,z2,z3,z7,z5,z10]),(0,[z1,z2,z3,z60,z5,z125]),(0,[z2,z3,z7,z5,z6,z1115]),(0,[z269,z2,z7,z181,z6,z10]),(0,[z497,z1,z2,z3,z11,z6]),(0,[z1,z612,z3,z7,z237,z6]),(0,[z150,z1,z2,z432,z7,z69])],[(0,[z918,z1,z2,z3,z7,z6])],[(0,[z62,z91,z1,z7,z21,z6])],[(0,[z1,z2,z3,z7,z5,z1116]),(0,[z1,z2,z3,z7,z5,z757])],[(0,[z1,z884,z3,z7,z5,z6]),(0,[z37,z2,z3,z53,z5,z6])],[(0,[z1,z2,z3,z366,z11,z16])],[(0,[z1,z2,z439,z60,z5,z6]),(0,[z1,z3,z7,z5,z6,z1117])],[(0,[z1,z332,z174,z7,z5,z6]),(0,[z1,z2,z7,z5,z6,z1118]),(0,[z1,z241,z3,z7,z11,z6])],[(0,[z1,z2,z3,z11,z10,z16])],[(0,[z1,z2,z3,z7,z5,z1119]),(0,[z1,z2,z3,z5,z854,z6])],[(0,[z1,z2,z3,z7,z1120,z6]),(0,[z1121,z2,z3,z7,z5,z6]),(0,[z74,z1,z2,z36,z17,z6]),(0,[z1,z2,z3,z36,z11,z6]),(0,[z1,z2,z3,z11,z6,z75])],[(0,[z166,z2,z3,z7,z1122,z6]),(0,[z37,z2,z3,z11,z6,z16]),(0,[z1123,z2,z3,z7,z5,z6])],[(0,[z1,z2,z1124,z7,z5,z6]),(0,[z71,z208,z1,z7,z5,z6]),(0,[z268,z2,z47,z7,z5,z6]),(0,[z86,z2,z3,z147,z5,z6]),(0,[z3,z7,z5,z579,z6,z10]),(0,[z12,z1,z3,z933,z5,z6])],[(0,[z445,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z1125,z6]),(0,[z86,z1,z2,z3,z935,z6]),(0,[z1126,z2,z3,z7,z5,z6]),(0,[z2,z760,z3,z7,z11,z6])],[(0,[z1,z3,z791,z7,z5,z6])]],
   [[(0,[z1,z2,z1127,z7,z5,z6]),(0,[z62,z1,z3,z7,z220,z6]),(0,[z2,z3,z7,z11,z6,z1128])],[(0,[z1,z2,z3,z50,z11,z6]),(0,[z1,z357,z174,z7,z5,z6]),(0,[z2,z3,z7,z5,z6,z1129]),(0,[z1,z2,z3,z133,z11,z6]),(0,[z1,z892,z3,z7,z5,z6])],[(0,[z86,z1,z2,z3,z11,z6]),(0,[z37,z332,z3,z7,z5,z6]),(0,[z2,z3,z11,z6,z10,z16]),(0,[z766,z2,z3,z7,z5,z40]),(0,[z1,z1130,z3,z7,z5,z6]),(0,[z1,z2,z3,z256,z17,z6])],[(0,[z1,z2,z3,z7,z5,z1131]),(0,[z37,z2,z337,z7,z5,z6]),(0,[z1,z2,z139,z240,z373,z6]),(0,[z768,z2,z3,z7,z11,z6])],[(0,[z1,z1132,z3,z7,z5,z6]),(0,[z1,z90,z7,z5,z6,z215])],[(0,[z1,z1133,z3,z7,z5,z6]),(0,[z1,z2,z139,z429,z5,z6])],[(0,[z436,z1,z3,z7,z5,z6]),(0,[z1,z2,z432,z7,z5,z6]),(0,[z2,z3,z133,z56,z11,z6]),(0,[z582,z1,z2,z3,z11,z6]),(0,[z192,z2,z3,z7,z5,z40])],[(0,[z1,z2,z3,z7,z1134,z6]),(0,[z12,z1,z3,z61,z11,z6]),(0,[z1,z2,z3,z133,z729,z6]),(0,[z2,z3,z7,z5,z6,z1128]),(0,[z2,z3,z7,z5,z6,z793])],[(0,[z1,z2,z1135,z7,z5,z6]),(0,[z2,z3,z7,z17,z40,z10])],[(0,[z1,z164,z3,z7,z17,z6]),(0,[z1,z1136,z3,z7,z5,z6]),(0,[z25,z1,z2,z3,z237,z16])],[(0,[z32,z3,z7,z5,z168,z6]),(0,[z1,z2,z3,z218,z11,z6]),(0,[z897,z2,z3,z5,z6,z10]),(0,[z1,z2,z3,z7,z1137,z6]),(0,[z901,z2,z3,z7,z5,z6])],[(0,[z86,z0,z2,z3,z11,z6]),(0,[z37,z357,z3,z7,z5,z6]),(0,[z2,z354,z7,z5,z155,z6]),(0,[z662,z1,z3,z7,z5,z22]),(0,[z1,z2,z3,z7,z1138,z6]),(0,[z1,z2,z85,z7,z237,z6])],[(0,[z163,z884,z3,z7,z5,z6]),(0,[z1,z2,z3,z1099,z5,z6]),(0,[z1139,z2,z3,z7,z5,z6]),(0,[z1,z241,z85,z7,z5,z6])],[(0,[z110,z1,z2,z3,z79,z6]),(0,[z238,z3,z7,z5,z6,z464]),(0,[z1,z2,z3,z7,z373,z6]),(0,[z1,z2,z139,z240,z232,z6]),(0,[z847,z2,z3,z7,z11,z6])],[(1,[z1,z2,z439,z11,z6]),(0,[z1,z1140,z3,z7,z5,z6]),(0,[z37,z2,z3,z7,z364,z6]),(0,[z1,z2,z3,z7,z1141,z6]),(0,[z188,z1,z2,z3,z11,z16]),(0,[z850,z1,z3,z7,z11,z6])],[(0,[z1,z2,z3,z210,z11,z6])]],
   [[(0,[z1142,z2,z3,z7,z5,z6])],[(0,[z1,z1143,z3,z7,z5,z6]),(0,[z1,z2,z3,z1144,z5,z6])],[(0,[z436,z3,z7,z5,z6,z10]),(0,[z37,z1140,z3,z7,z5,z6])],[(0,[z74,z1,z2,z36,z11,z6]),(0,[z1,z3,z7,z11,z6,z1145])],[(0,[z1,z140,z3,z7,z5,z6]),(0,[z1,z2,z1146,z7,z5,z6])],[(0,[z1,z2,z3,z7,z5,z1147]),(0,[z2,z3,z7,z1148,z5,z6]),(0,[z68,z2,z3,z7,z153,z6])],[(0,[z1,z2,z7,z5,z6,z1149]),(0,[z1,z38,z3,z562,z5,z6]),(0,[z1,z2,z7,z5,z900,z30])],[(0,[z1,z2,z3,z5,z6,z927]),(0,[z1,z2,z3,z339,z5,z6]),(0,[z1,z2,z3,z813,z5,z6]),(0,[z734,z2,z3,z7,z6,z10]),(0,[z1,z2,z3,z7,z232,z6])],[(0,[z1,z2,z3,z7,z1150,z6]),(0,[z1,z38,z266,z7,z5,z6]),(0,[z1,z2,z3,z67,z952,z6]),(0,[z598,z1,z2,z7,z181,z6])],[(0,[z58,z2,z179,z7,z11,z6]),(0,[z166,z2,z3,z7,z97,z6]),(0,[z1,z2,z3,z7,z1151,z6]),(0,[z1,z2,z1152,z7,z5,z6]),(0,[z192,z2,z3,z7,z130,z6])],[(0,[z134,z3,z156,z7,z5,z6]),(0,[z1,z2,z3,z78,z11,z6]),(0,[z37,z2,z3,z118,z5,z6]),(0,[z2,z3,z7,z1088,z11,z6]),(0,[z1,z2,z3,z82,z11,z6]),(0,[z436,z1,z7,z94,z5,z6]),(0,[z1,z2,z3,z7,z5,z900]),(0,[z1,z2,z3,z256,z11,z6]),(0,[z1,z3,z7,z5,z6,z1145])],[(0,[z2,z3,z56,z11,z6,z16]),(0,[z792,z2,z3,z7,z11,z6])],[(0,[z1153,z2,z3,z7,z5,z6]),(0,[z1,z2,z1154,z7,z5,z6])],[(0,[z1,z2,z266,z7,z17,z6]),(0,[z1155,z2,z3,z7,z5,z6])],[(0,[z1156,z2,z3,z7,z5,z6]),(0,[z1,z2,z7,z1157,z5,z6])],[(0,[z1,z2,z3,z196,z17,z6])]],
   [[(0,[z1,z2,z3,z7,z5,z1158]),(0,[z1159,z2,z3,z7,z5,z6]),(0,[z1,z2,z976,z7,z5,z6])],[(0,[z1,z1160,z3,z7,z5,z6]),(0,[z86,z37,z2,z3,z11,z6]),(0,[z2,z54,z7,z94,z6,z10]),(0,[z37,z2,z3,z180,z5,z6]),(0,[z72,z1,z7,z5,z6,z293]),(0,[z650,z1,z2,z3,z11,z6]),(0,[z2,z9,z7,z5,z141,z459])],[(0,[z1,z2,z3,z7,z5,z1161]),(0,[z1,z2,z3,z1162,z5,z6]),(0,[z1,z2,z1163,z7,z5,z6]),(0,[z1,z2,z3,z952,z11,z6]),(0,[z1,z1164,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z1165,z6]),(0,[z62,z1,z3,z118,z21,z6])],[(0,[z2,z3,z36,z11,z6,z10]),(0,[z1166,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z133,z11,z40])],[(0,[z2,z3,z7,z130,z6,z10]),(0,[z436,z37,z3,z7,z5,z6]),(0,[z1,z2,z1167,z7,z5,z6]),(0,[z1,z2,z3,z127,z11,z6]),(1,[z1,z2,z715,z5,z6]),(0,[z1,z2,z390,z7,z5,z6]),(0,[z1,z3,z7,z487,z373,z6]),(0,[z871,z1,z2,z3,z7,z11])],[(0,[z58,z2,z292,z7,z5,z6]),(0,[z2,z3,z7,z17,z6,z10]),(0,[z1,z2,z36,z377,z11,z6]),(0,[z591,z1,z2,z3,z11,z6])],[(0,[z1,z2,z240,z36,z11,z6]),(0,[z1,z2,z139,z482,z5,z6]),(0,[z2,z3,z7,z11,z1168,z6]),(0,[z1,z2,z7,z17,z1064,z6]),(0,[z1,z209,z417,z7,z5,z6])],[(0,[z1,z2,z3,z11,z6,z244]),(0,[z1,z2,z417,z291,z5,z6])],[(0,[z650,z2,z179,z7,z5,z6]),(0,[z212,z2,z3,z7,z17,z6]),(0,[z870,z1,z2,z3,z7,z5])],[(0,[z163,z109,z3,z7,z5,z6])],[(0,[z37,z2,z3,z7,z5,z81]),(0,[z2,z3,z7,z13,z6,z10]),(0,[z308,z2,z3,z7,z11,z6])],[(0,[z1,z2,z791,z7,z5,z6])],[(0,[z1,z2,z3,z7,z1169,z6]),(0,[z68,z0,z2,z3,z11,z6]),(0,[z2,z3,z118,z5,z6,z10]),(0,[z1,z2,z1170,z7,z5,z6]),(0,[z1,z2,z3,z36,z213,z6]),(0,[z1,z1171,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z1172,z6]),(0,[z150,z1,z2,z417,z7,z69])],[(0,[z2,z670,z3,z7,z5,z10]),(0,[z2,z3,z7,z5,z1122,z6]),(0,[z2,z3,z7,z5,z1168,z6]),(0,[z2,z3,z1011,z7,z5,z6])],[(0,[z675,z1,z2,z3,z11,z6]),(0,[z86,z2,z3,z4,z5,z6]),(0,[z1,z2,z1173,z7,z5,z6]),(0,[z1,z3,z7,z487,z232,z6])]],
   [[(0,[z1174,z1,z2,z7,z5,z6]),(0,[z1,z2,z3,z7,z1100,z6]),(0,[z1014,z2,z3,z7,z5,z6]),(0,[z1,z231,z3,z7,z17,z6]),(0,[z2,z3,z7,z5,z6,z1175]),(0,[z943,z2,z3,z7,z5,z6]),(0,[z832,z1,z2,z7,z17,z6]),(0,[z522,z1,z2,z7,z18,z6])],[(0,[z1176,z1,z2,z7,z5,z6]),(0,[z0,z2,z3,z639,z5,z6]),(0,[z38,z3,z67,z5,z6,z10]),(0,[z37,z2,z7,z5,z449,z6]),(0,[z361,z2,z3,z7,z96,z33])],[(0,[z1,z2,z3,z7,z1177,z6]),(0,[z2,z3,z7,z5,z538,z10]),(0,[z2,z3,z7,z5,z10,z223]),(0,[z12,z1,z3,z61,z17,z6]),(0,[z63,z1,z2,z36,z5,z6])],[(0,[z1,z2,z3,z562,z11,z6])],[(0,[z23,z3,z7,z5,z6,z10]),(0,[z1,z23,z432,z7,z5,z6])],[(0,[z1,z2,z266,z7,z11,z6]),(0,[z1178,z2,z3,z7,z5,z6])],[(0,[z163,z446,z109,z7,z5,z6]),(0,[z3,z7,z5,z6,z10,z365]),(0,[z112,z72,z169,z7,z5,z6]),(0,[z844,z2,z3,z7,z17,z6])],[(0,[z1,z2,z3,z7,z1179,z6]),(0,[z74,z1,z2,z36,z364,z6]),(0,[z1,z1180,z3,z7,z5,z6]),(0,[z1,z2,z3,z196,z11,z6]),(0,[z1,z2,z3,z7,z366,z142]),(0,[z192,z2,z3,z7,z237,z6])],[(0,[z1,z1181,z3,z7,z5,z6]),(0,[z322,z2,z139,z7,z5,z6]),(0,[z192,z241,z3,z7,z5,z6])],[(0,[z1,z707,z3,z7,z5,z6]),(0,[z1,z1182,z3,z7,z5,z6]),(0,[z2,z3,z7,z5,z10,z423]),(0,[z1,z2,z7,z1183,z5,z6]),(0,[z1,z2,z3,z202,z11,z6])],[(0,[z1,z2,z3,z7,z1184,z6]),(0,[z1,z266,z7,z61,z5,z6]),(0,[z68,z2,z3,z240,z11,z6])],[(0,[z1,z2,z3,z5,z1185,z6]),(0,[z2,z3,z7,z5,z10,z425]),(0,[z91,z2,z7,z5,z6,z10]),(0,[z2,z3,z7,z5,z6,z1186]),(0,[z2,z3,z7,z17,z56,z6])],[(0,[z1,z211,z634,z7,z5,z6]),(0,[z86,z1,z2,z174,z11,z6]),(0,[z1,z2,z3,z196,z181,z6]),(0,[z68,z2,z3,z17,z11,z6])],[(0,[z0,z2,z3,z11,z6,z10]),(1,[z2,z3,z7,z5,z775]),(0,[z2,z3,z7,z5,z556,z10]),(0,[z2,z3,z180,z5,z6,z10]),(0,[z1,z209,z3,z7,z17,z6])],[(0,[z1,z2,z3,z1187,z5,z6]),(0,[z86,z2,z3,z512,z5,z6]),(0,[z1,z2,z3,z1188,z5,z6]),(0,[z2,z3,z7,z5,z6,z1189]),(0,[z358,z1,z2,z7,z5,z30]),(0,[z1,z2,z3,z291,z17,z6])],[(0,[z1,z2,z714,z7,z5,z6]),(0,[z37,z2,z3,z7,z5,z310]),(0,[z1,z2,z139,z240,z5,z6]),(0,[z1,z1190,z3,z7,z5,z6])]],
   [[(0,[z308,z2,z417,z7,z5,z6])],[(0,[z1,z2,z7,z5,z1191,z6]),(0,[z86,z2,z3,z398,z5,z6]),(0,[z1,z720,z2,z7,z5,z6]),(0,[z212,z2,z3,z7,z11,z6]),(0,[z1,z2,z3,z227,z11,z6])],[(0,[z510,z1,z2,z3,z11,z6]),(0,[z1,z2,z3,z7,z5,z1192]),(0,[z37,z2,z3,z36,z11,z6]),(0,[z72,z1,z169,z7,z5,z6]),(0,[z1193,z2,z3,z7,z5,z6])],[(0,[z68,z2,z3,z7,z320,z6]),(0,[z1,z2,z3,z7,z321,z158]),(0,[z1,z2,z3,z7,z724,z6]),(0,[z1,z2,z3,z1194,z5,z6]),(0,[z216,z2,z7,z5,z6,z217])],[(0,[z58,z2,z179,z7,z17,z6]),(0,[z582,z2,z3,z7,z5,z10]),(0,[z1,z2,z3,z17,z616,z6])],[(0,[z359,z2,z3,z7,z5,z6]),(0,[z264,z1,z2,z3,z79,z6]),(0,[z1,z2,z3,z1195,z5,z6]),(0,[z74,z1,z2,z36,z213,z6])],[(0,[z1,z2,z3,z7,z1196,z6]),(0,[z1,z2,z3,z60,z17,z6]),(0,[z251,z1,z2,z3,z7,z105])],[(0,[z1,z2,z3,z7,z320,z158])],[(0,[z37,z2,z3,z133,z11,z6]),(0,[z1,z2,z3,z1197,z5,z6]),(0,[z72,z1,z395,z7,z5,z6]),(0,[z1,z2,z3,z7,z1198,z6]),(0,[z1,z337,z7,z5,z6,z22]),(0,[z1,z231,z3,z7,z11,z6])],[(0,[z1,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z1199,z6]),(0,[z1,z731,z3,z7,z5,z6]),(0,[z2,z3,z7,z5,z6,z1200]),(0,[z1,z3,z7,z17,z579,z6])],[(0,[z1,z2,z3,z7,z1201,z6]),(0,[z1,z2,z3,z7,z5,z1034])],[(0,[z2,z3,z53,z5,z6,z10]),(0,[z1,z2,z3,z7,z1202,z6]),(0,[z1,z3,z61,z221,z11,z6]),(0,[z1,z3,z7,z17,z6,z365])],[(0,[z71,z108,z2,z7,z5,z6]),(0,[z1,z2,z3,z7,z5,z1203])],[(0,[z1,z2,z439,z7,z5,z158]),(0,[z148,z1,z2,z3,z11,z6]),(0,[z37,z2,z432,z7,z5,z6]),(0,[z1,z2,z3,z1204,z5,z6]),(0,[z1205,z2,z3,z7,z5,z6]),(0,[z25,z1,z241,z3,z5,z16])],[(0,[z274,z1,z2,z3,z11,z6])],[(0,[z1,z3,z7,z5,z6,z1206])]],
   [[(0,[z208,z322,z3,z7,z5,z6]),(0,[z2,z3,z7,z5,z6,z1207]),(0,[z37,z1136,z3,z7,z5,z6]),(0,[z1,z38,z3,z67,z5,z6])],[(0,[z1,z2,z3,z7,z5,z1208]),(0,[z332,z3,z7,z5,z6,z10]),(0,[z1209,z2,z3,z7,z5,z6])],[(0,[z72,z1,z2,z36,z11,z6]),(0,[z426,z1,z3,z7,z443,z6])],[(0,[z108,z2,z7,z5,z6,z10]),(0,[z1,z2,z3,z7,z1210,z6])],[(0,[z241,z3,z7,z5,z6,z10]),(0,[z37,z2,z3,z7,z373,z6]),(0,[z932,z2,z3,z7,z11,z6])],[(0,[z1,z2,z1211,z7,z5,z6]),(0,[z1,z2,z3,z7,z1212,z6]),(0,[z1,z209,z3,z7,z11,z6])],[(0,[z1,z2,z3,z7,z1122,z6]),(0,[z27,z1,z3,z7,z5,z757]),(0,[z1,z2,z3,z291,z11,z6]),(0,[z2,z3,z7,z11,z6,z523]),(0,[z308,z2,z3,z7,z17,z6])],[(0,[z2,z47,z7,z5,z155,z6]),(0,[z1,z2,z3,z439,z11,z6]),(0,[z2,z986,z7,z5,z6,z10])],[(0,[z37,z1143,z3,z7,z5,z6]),(0,[z1,z2,z3,z297,z11,z6])],[(0,[z134,z32,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z17,z158]),(0,[z0,z2,z3,z5,z56,z6])],[(0,[z208,z3,z7,z5,z6,z10]),(0,[z1,z2,z3,z7,z1213,z6]),(0,[z2,z3,z7,z5,z137,z10]),(0,[z1,z211,z90,z7,z5,z6]),(0,[z2,z3,z7,z5,z6,z1214])],[(0,[z37,z140,z3,z7,z5,z6]),(0,[z2,z3,z7,z5,z6,z1215]),(0,[z1,z3,z7,z1216,z5,z6]),(0,[z1,z893,z3,z7,z17,z6])],[(0,[z37,z2,z3,z7,z5,z558]),(0,[z597,z32,z3,z7,z5,z6]),(0,[z150,z1,z209,z3,z7,z69])],[(0,[z2,z3,z7,z5,z6,z523]),(0,[z1,z1217,z3,z7,z5,z6]),(0,[z1,z3,z7,z5,z6,z1218]),(0,[z1,z2,z3,z7,z202,z263])],[(0,[z37,z2,z3,z339,z5,z6]),(0,[z37,z2,z3,z7,z232,z6]),(0,[z1,z2,z3,z7,z5,z1219])],[(0,[z37,z2,z3,z7,z5,z576]),(0,[z1,z2,z3,z7,z229,z6]),(0,[z2,z3,z7,z5,z6,z1220]),(0,[z625,z2,z432,z7,z5,z6])]],
   [[(0,[z2,z139,z240,z5,z6,z10]),(0,[z89,z2,z3,z5,z6,z405]),(0,[z1,z3,z7,z5,z861,z6]),(0,[z216,z2,z3,z7,z17,z6])],[(0,[z2,z3,z7,z1122,z167,z6]),(0,[z72,z37,z169,z7,z5,z6]),(0,[z1,z3,z7,z487,z5,z6])],[(0,[z1,z2,z3,z7,z321,z125]),(0,[z2,z3,z7,z5,z637,z10]),(0,[z1,z2,z3,z1221,z5,z6]),(0,[z1,z3,z7,z1222,z5,z6]),(0,[z1,z9,z7,z5,z141,z365])],[(0,[z1,z1223,z3,z7,z5,z6]),(0,[z34,z3,z7,z5,z65,z10]),(0,[z2,z3,z7,z1137,z6,z10]),(0,[z89,z1,z2,z3,z5,z16]),(0,[z1,z860,z3,z7,z5,z6]),(0,[z1,z90,z3,z61,z11,z6]),(0,[z1,z2,z1224,z7,z5,z6])],[(0,[z1,z2,z7,z1225,z5,z6])],[(0,[z1,z2,z3,z1226,z5,z6]),(0,[z1227,z2,z3,z7,z5,z6]),(0,[z1228,z2,z3,z7,z5,z6]),(0,[z1,z3,z7,z5,z6,z1229]),(0,[z1,z2,z9,z7,z11,z141])],[(0,[z134,z884,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z320,z125]),(0,[z261,z1,z2,z3,z11,z6])],[(0,[z1,z2,z3,z1230,z5,z6]),(0,[z1231,z2,z3,z7,z5,z6])],[(0,[z1,z2,z439,z7,z321,z6]),(0,[z72,z1,z3,z61,z11,z6]),(0,[z1,z2,z571,z7,z297,z6])],[(0,[z2,z3,z7,z5,z506,z10]),(0,[z1,z2,z3,z7,z1232,z6]),(0,[z1,z2,z3,z11,z6,z568])],[(0,[z103,z2,z3,z7,z11,z10]),(0,[z322,z2,z7,z36,z5,z6]),(1,[z1,z791,z7,z5,z6]),(0,[z2,z3,z7,z5,z6,z1233])],[(0,[z1,z1234,z3,z7,z5,z6]),(0,[z273,z301,z3,z7,z5,z6]),(0,[z598,z1,z2,z36,z11,z6])],[(0,[z1,z2,z439,z7,z320,z6]),(0,[z1,z2,z439,z7,z5,z125]),(0,[z86,z2,z174,z4,z5,z6]),(0,[z37,z2,z3,z7,z5,z41]),(0,[z148,z37,z2,z3,z11,z6]),(0,[z37,z2,z390,z7,z5,z6])],[(0,[z1,z446,z2,z7,z5,z6]),(0,[z71,z2,z655,z7,z5,z6]),(0,[z492,z1,z2,z3,z11,z6]),(0,[z1,z2,z3,z67,z11,z6]),(0,[z426,z1,z3,z61,z11,z6]),(0,[z1,z2,z36,z11,z6,z30]),(0,[z68,z2,z3,z7,z11,z6]),(0,[z1,z1081,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z1235,z6]),(0,[z1,z2,z3,z715,z5,z6])],[(0,[z1236,z2,z3,z7,z5,z6])]],
   [[(0,[z492,z2,z3,z639,z5,z6]),(0,[z2,z3,z7,z5,z81,z775]),(0,[z106,z2,z390,z7,z5,z6])],[(0,[z0,z1,z2,z3,z11,z6]),(0,[z1,z2,z3,z7,z11,z158]),(0,[z1,z2,z7,z715,z5,z6]),(0,[z1,z2,z3,z17,z745,z6])],[(0,[z1,z2,z3,z7,z1237,z6]),(0,[z1,z2,z1238,z7,z5,z6]),(0,[z924,z2,z3,z7,z5,z6]),(0,[z1,z2,z3,z7,z96,z33])],[(0,[z1,z2,z3,z7,z1239,z6]),(0,[z1,z2,z3,z7,z97,z6]),(0,[z1,z3,z933,z61,z5,z6])],[(0,[z376,z2,z3,z7,z162,z6]),(0,[z72,z544,z1,z7,z5,z6]),(0,[z696,z1,z2,z3,z11,z6]),(0,[z1240,z2,z3,z7,z5,z6]),(0,[z1241,z2,z3,z7,z5,z6])],[(0,[z1,z3,z7,z1242,z5,z6]),(0,[z1,z1243,z3,z7,z5,z6]),(0,[z1244,z2,z3,z7,z5,z6]),(0,[z31,z2,z3,z56,z11,z6]),(0,[z1,z2,z3,z374,z11,z6])],[(0,[z0,z2,z3,z111,z5,z6]),(0,[z1,z332,z3,z60,z5,z6]),(0,[z1,z2,z3,z53,z441,z6])],[(0,[z2,z3,z7,z5,z6,z1245]),(0,[z1,z23,z3,z7,z5,z6])],[(0,[z1,z2,z3,z7,z17,z125]),(0,[z1,z2,z3,z601,z17,z6]),(0,[z779,z3,z7,z5,z6,z10]),(0,[z1,z2,z3,z380,z11,z6]),(0,[z216,z2,z3,z7,z11,z6]),(0,[z68,z31,z2,z3,z11,z6])],[(0,[z1,z2,z3,z7,z5,z1246])],[(0,[z1,z2,z1247,z7,z5,z6]),(0,[z2,z3,z7,z5,z689,z10]),(0,[z1,z211,z2,z36,z11,z6]),(0,[z1,z38,z3,z933,z5,z6]),(0,[z306,z2,z3,z7,z11,z6])],[(0,[z1,z1248,z3,z7,z5,z6]),(0,[z114,z2,z9,z7,z5,z141])],[(0,[z1,z2,z3,z7,z1249,z6]),(0,[z37,z2,z3,z7,z5,z203]),(0,[z2,z3,z7,z5,z6,z1250])],[(0,[z980,z1,z2,z3,z5,z6]),(0,[z2,z3,z7,z11,z6,z83])],[(0,[z1,z2,z3,z7,z5,z1251]),(0,[z71,z2,z47,z7,z5,z6]),(0,[z1,z1252,z2,z7,z5,z6]),(0,[z62,z1,z7,z449,z21,z6]),(0,[z1253,z2,z3,z7,z5,z6])],[]]]

def SA : ℕ × List W → Bool := fun c => !inB2 8 256 bkA c

def SB : ℕ × List W → Bool := fun c => !inB2 16 512 bkB c

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
theorem pb0 : chunkB SB 1 ((bkA.flatten.flatten.drop 0).take 494) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb1 : chunkB SB 1 ((bkA.flatten.flatten.drop 494).take 498) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 992).take 418) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1410)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [494, 498, 418] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 142).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 142).take 134).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc2 : chunkOK 5 ((bkB.flatten.drop 276).take 141).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc3 : chunkOK 5 ((bkB.flatten.drop 417).take 95).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 512)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [142, 134, 141, 95] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_cons pc2 (windowsF_cons pc3 (windowsF_nil pcend))))

theorem reject : search 8 rows = false :=
  search_false_C2 (dp := 0) (J := 5) (d := 2) (g1 := 8) (nb1 := 256) (g2 := 16) (nb2 := 512) (by norm_num) gf windowsC windowsB windowsA

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

end PEqualNP.Outside.L_meta_37255

theorem PEqualNP.Outside.L_meta_37255 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4277071594 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4277071594 * 2 ^ 32 + 4276150496) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_37255.solve