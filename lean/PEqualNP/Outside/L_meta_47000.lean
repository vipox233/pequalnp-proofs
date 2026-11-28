import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47000

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
  Nat.testBit (3941264040 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

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
  [(0x0a52450014a48a45#64 ++ 0x20000180ca03294a#64 ++ 0x3fffffe07fffffff#64 ++ 0xfff387c3ff0fffff#64 : BitVec 256),
   (0xc0a0a265814144a2#64 ++ 0x4e89723911e44631#64 ++ 0xc1f1e3ff83e3c7e3#64 ++ 0xeffd7a3d13f44e73#64 : BitVec 256),
   (0x540128aaa8025128#64 ++ 0x86866c3614d85294#64 ++ 0xfe01fcfffc03f9fc#64 ++ 0xfe8e7c3e1cf8739c#64 : BitVec 256),
   (0xa73400d34e6801d0#64 ++ 0x0aaf802fa0be83e0#64 ++ 0xfffe00fffffc01ff#64 ++ 0x0aaf803fe0ff83e0#64 : BitVec 256),
   (0x000000fc7393a000#64 ++ 0x0c4fdf40007dfc00#64 ++ 0x000000fffffffe00#64 ++ 0x0ccfffc000fffc00#64 : BitVec 256),
   (0x39c9d00000000000#64 ++ 0x090fbedf7f000000#64 ++ 0xffffff0000000000#64 ++ 0x0f0fffffff000000#64 : BitVec 256)]

def witness : Circuit :=
  ⟨[⟨.and, [1, 2]⟩, ⟨.or, [0, 6]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [0, 8]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [9, 10]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [12, 5]⟩, ⟨.or, [11, 13]⟩, ⟨.and, [7, 14]⟩], 15⟩

def mkw (a b c d : BitVec 64) : W := a ++ b ++ c ++ d

def z0 : W := mkw 0x0000006401010000 0x0c09520000644400 0x000000ff83e3c600 0x0ccd7a0000f44c00

def z1 : W := mkw 0x0a52450004240a45 0x20000080ca02014a 0x3fffff00000001ff 0xf3300003ff0003ff

def z2 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x3fffffe07fffffff 0xfff387c3ff0fffff

def z3 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffff0000000000 0x0f0fffffff000000

def z4 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z5 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z6 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z7 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x000000fffffffe00 0x0ccfffc000fffc00

def z8 : W := mkw 0xa73400d34e6801d0 0x02a0002fa0be83e0 0xfffe00fffffc01ff 0x02a0003fe0ff83e0

def z9 : W := mkw 0x0080806401010000 0x0c09721911644400 0xc1f1e3ff83e3c600 0x0fcd7a3d13f44c00

def z10 : W := mkw 0x000000a820020000 0x04064c0000585000 0x000000fffc03f800 0x0c8e7c0000f87000

def z11 : W := mkw 0x540128fefb93f128 0x8ecfff7614fdfe94 0xfe01fcfffffffffc 0xfecffffe1cffff9c

def z12 : W := mkw 0x1401088a28021108 0x80060c0604181084 0x3e001c007c00381c 0x100204020c08318c

def z13 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xc000001f80000000 0x000c783c00f00000

def z14 : W := mkw 0xaf7645030c6c0bd5 0x22a000afea8203ea 0xffffff00000001ff 0xf330003fff0003ff

def z15 : W := mkw 0x7dc9f8aaa8025128 0x8f8ffeff7fd85294 0xfffffffffc03f9fc 0xff8ffffffff8739c

def z16 : W := mkw 0xc0202061804040a0 0x0e89603910e44230 0xc1f1e0ff83e3c1e3 0xeead783d10f44270

def z17 : W := mkw 0x18c9d02c3193a000 0x05407fd05f417c00 0x0001ff000003fe00 0x05407fc01f007c00

def z18 : W := mkw 0x0842450010848a05 0x200001804a01280a 0x0001ff000003fe00 0xf55007c01f007c1f

def z19 : W := mkw 0xaf7645d35eec8bd5 0x2aaf81afeabfabea 0xffffffffffffffff 0xffff87ffffffffff

def z20 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfe0e001ffc1c001c 0x000e803ee0fb8180

def z21 : W := mkw 0x750128aaa8025128 0x8e8fec3f34d85294 0xfffffcfffc03f9fc 0xfe8ffc3ffcf8739c

def z22 : W := mkw 0x0080800000000000 0x0809321911000000 0xc1f1e30000000000 0x0f0d7a3d13000000

def z23 : W := mkw 0xc0202265814144a2 0x4680402000e44631 0x000000ff83e3c7e3 0xe0f0000000f44e73

def z24 : W := mkw 0x29c8d00000000000 0x090f92cf6b000000 0xfffe030000000000 0x0b0f83ffe3000000

def z25 : W := mkw 0x4ad2e72495a5ce67 0x64007390db436d5b 0x3fffffe07fffffff 0xfff3ffc3ff0fffff

def z26 : W := mkw 0x100100a820020000 0x04066c1614585000 0xfe01fcfffc03f800 0x0e8e7c3e1cf87000

def z27 : W := mkw 0x0000008820020000 0x00060c0000181000 0x000000007c003800 0x0002040000083000

def z28 : W := mkw 0x250400924a080110 0x0026800620188080 0x0000000000000000 0x0000000000000000

def z29 : W := mkw 0xa52400d34a480190 0x0aaf802f20bc82a0 0xc1f000ff83e001e3 0x0aad003d00f40260

def z30 : W := mkw 0x000000b87292a000 0x0446cd400059f800 0x000000fffc1ff800 0x0c8efdc000fbf000

def z31 : W := mkw 0x80a0824501410482 0x4809120901240421 0x01f0030003e00603 0x0171020103040c63

def z32 : W := mkw 0x1001000000000000 0x080fbe5614000000 0xfe01fc0000000000 0x0e0ffffe1c000000

def z33 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x3e0e1c007c1c381c 0x100285c2ec0bb18c

def z34 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc000001f80000000 0x000c783c00f00000

def z35 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x3e01fcfffffffffc 0xfecfffc21cffff9c

def z36 : W := mkw 0x0000002c3193a000 0x0c4fdf4000417c00 0x000000000003fe00 0x0c4fffc000007c00

def z37 : W := mkw 0x0400008208000100 0x0286002600980280 0xfe0000fffc0001fc 0x0a8e003e00f80380

def z38 : W := mkw 0xe7b4a2f7cf6945f2 0x4eaff23fb1fec7f1 0xffffe3ffffffc7ff 0xeffffa3ff3ffcff3

def z39 : W := mkw 0xc0a0a265814144a2 0x4e8ffe7911e44631 0xc1f1e3ff83e3c7e3 0xeffffffd13f44e73

def z40 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f0031f83e00603 0x017d7a3d03f40c63

def z41 : W := mkw 0x29c8d00000000000 0x090992c96b000000 0x01fe030000000000 0x010183c1e3000000

def z42 : W := mkw 0xc0a0a265814144a2 0x4680723011e44631 0x0001e3ff83e3c7e3 0xe5f07a0013f44e73

def z43 : W := mkw 0xa7b482d74f6905d2 0x4aaf922fa1be87e1 0xfffe03fffffc07ff 0x0bff823fe3ff8fe3

def z44 : W := mkw 0x0000000000000000 0x00060c0000000000 0x0000000000000000 0x0c0e7c0000000000

def z45 : W := mkw 0xa73400d34e6801d0 0x0aaf9e6fa0be83e0 0xfffe00fffffc01ff 0x0eafffffe0ff83e0

def z46 : W := mkw 0x0a5245fc77b7aa45 0x24404180ca7ffd4a 0x3fffffffffffffff 0xfff387c3ffffffff

def z47 : W := mkw 0x0000002c3193a000 0x04405f4000417c00 0x000000000003fe00 0x04407fc000007c00

def z48 : W := mkw 0x000000fc7393a000 0x04404100007dfc00 0x000000fffffffe00 0x00c0000000fffc00

def z49 : W := mkw 0x0000000000000000 0x0000000000000000 0x3e01fce07c03f9fc 0xfe8204021c08739c

def z50 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xc1fe001f83fc0003 0x002d803de0f78060

def z51 : W := mkw 0x0000006401010000 0x0c0fde4000644400 0x000000ff83e3c600 0x0ccfffc000f44c00

def z52 : W := mkw 0x000000fc63132000 0x0c4fde40007cd400 0x0000001f80000000 0x000c780000f00000

def z53 : W := mkw 0x0a5245fc77b7aa45 0x2c4fdfc0ca7ffd4a 0x3fffffffffffffff 0xffffffc3ffffffff

def z54 : W := mkw 0xc0a0a2fdf3d3e4a2 0x4ecfff7911fdfe31 0xc1f1e3ffffffffe3 0xeffffffd13fffe73

def z55 : W := mkw 0x000000d042000000 0x080f8000003c8000 0x000000fffffc0000 0x088f800000ff8000

def z56 : W := mkw 0xc0a0a201804044a2 0x4280203911800231 0xc1f1e300000001e3 0xe330003d13000273

def z57 : W := mkw 0x5401288aa8025128 0x82862c3614981294 0xfe01fc007c0039fc 0xf202043e1c08339c

def z58 : W := mkw 0x3949500000000000 0x01068cc66e000000 0x3e0e1c0000000000 0x000285c2ec000000

def z59 : W := mkw 0x3bdbd50014a48a45 0x290fbfdfff03294a 0xffffffe07fffffff 0xffffffffff0fffff

def z60 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe01fc1f80000000 0x0e0e7c3e1cf00000

def z61 : W := mkw 0x000000fc63132000 0x0c4fde40007cd400 0x000000fffc03f800 0x0c8e7c0000f87000

def z62 : W := mkw 0x29c8d00000000000 0x0909b2d97b000000 0xc1ffe30000000000 0x0f0dfbfdf3000000

def z63 : W := mkw 0x0000000000000000 0x080f800000000000 0x0000000000000000 0x080f800000000000

def z64 : W := mkw 0x1001000000000000 0x00062c1614000000 0xfe01fc0000000000 0x0e0e7c3e1c000000

def z65 : W := mkw 0x000000fc7393a000 0x04405f40007dfc00 0x000000fffffffe00 0x04c07fc000fffc00

def z66 : W := mkw 0x210000d042000000 0x080f800f203c8000 0xfffe00fffffc0000 0x0a8f803fe0ff8000

def z67 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffffcfffffff9ff 0xfeaf843ffcfff3fc

def z68 : W := mkw 0x48c2e7249185ce27 0x640073905b416c1b 0x0001ff000003fe00 0xf5507fc01f007c1f

def z69 : W := mkw 0x271400924e280150 0x02a68026a09a83c0 0xfe0e00fffc1c01fc 0x0a8e803ee0fb8380

def z70 : W := mkw 0xbffdd0d34e6801d0 0x0bafa0bfffbe83e0 0xfffffffffffc01ff 0x0baf803fffff83e0

def z71 : W := mkw 0x0210000004200040 0x0000000080020140 0x3ffe00e07ffc01ff 0x0aa38003e00f83e0

def z72 : W := mkw 0x3949500000000000 0x01068cc66e000000 0x3fffff0000000000 0x0f0387c3ff000000

def z73 : W := mkw 0xa73400ff6f7b21d0 0x0eefde6fa0fed7e0 0xfffe00fffffc01ff 0x0aaff83fe0ff83e0

def z74 : W := mkw 0xd4a1aaaba84255aa 0xc6866c3f15d852b5 0xfff1fffffc03f9ff 0xffbe7c3f1ff873ff

def z75 : W := mkw 0x0840400000000000 0x000000804a000000 0x3fffff0000000000 0x0f0387c3ff000000

def z76 : W := mkw 0x1401088a28021108 0x80060c0604181084 0x3e01fce07c03f9fc 0xfe8204021c08739c

def z77 : W := mkw 0x4080a02080004020 0x0e89723911c04210 0xc1f1e3ff8003c1e0 0xef8d7a3d13f04210

def z78 : W := mkw 0x8af2c74515e58ec7 0x68091389cb272d6b 0x01fe030003fc0603 0x017183c1e3078c63

def z79 : W := mkw 0xcaf2e76595e5cee7 0x6e8973b9dbe76f7b 0xffffffffffffffff 0xffffffffffffffff

def z80 : W := mkw 0x39c9d00000000000 0x090f9ecf6f000000 0x3ffe1f0000000000 0x010387c3ef000000

def z81 : W := mkw 0xb73508db6e6a11d8 0x8aaf8c2fa4be93e4 0xfffe1cfffffc39ff 0x1aaf843fecffb3ec

def z82 : W := mkw 0x7dc9f8fefb93f128 0x8fcfffff7ffdfe94 0xfffffffffffffffc 0xffcfffffffffff9c

def z83 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x000e0000001c0000 0x000081c0e0038000

def z84 : W := mkw 0x271400924e280150 0x00268006a01a81c0 0x3e0e00007c1c001c 0x00028002e00b8180

def z85 : W := mkw 0x4080a22481014422 0x4400721011404411 0x0001e3000003c600 0xe5507a0013004c13

def z86 : W := mkw 0x50012828a0025028 0x84006c1014405014 0x0001fc000003f800 0xf4007c001c00701c

def z87 : W := mkw 0xa3340051466800d0 0x08298009a0268160 0x01fe000003fc0003 0x00218001e0078060

def z88 : W := mkw 0x3715089a6e2a1158 0x80268c06a41a91c4 0x3e0e1c007c1c381c 0x10028402ec0bb18c

def z89 : W := mkw 0x2314001046280050 0x00208000a0028140 0x000e0000001c0000 0x00008000e0038000

def z90 : W := mkw 0x0000000000000000 0x0000000000000000 0x01f1e3e003e3c7e3 0xeff1020113044e73

def z91 : W := mkw 0x0a5245fc77b7aa45 0x2c4fdfc0ca7ffd4a 0x3e0e1cfffffffe1c 0x1ccfffc2ecfffd8c

def z92 : W := mkw 0x400020fcf393e020 0x0ecfff7010fdfe10 0xc001e0ffffffffe0 0xeecffffc10fffe10

def z93 : W := mkw 0x0000000010808000 0x0000010000012800 0x000000e07ffffe00 0x0cc387c0000ffc00

def z94 : W := mkw 0x39c9d00000000000 0x0106acdf7f000000 0xffffff0000000000 0x030285ffff000000

def z95 : W := mkw 0x3189900000000000 0x090fbe5f35000000 0xc000000000000000 0x000c783c00000000

def z96 : W := mkw 0x863400d34e6801d0 0x0aa9002980be83e0 0xc1f000fffffc01ff 0x0aad003d00ff83e0

def z97 : W := mkw 0x0000000010808000 0x0000010000012800 0x000000007c1c3800 0x000285c0000bb000

def z98 : W := mkw 0x0a52450014a48a45 0x280f9fc0ca03294a 0x3fffffe07fffffff 0xffffffc3ff0fffff

def z99 : W := mkw 0x000000545391a000 0x004001000025ac00 0x0000000003fc0600 0x0040000000078c00

def z100 : W := mkw 0x0840400000000000 0x000000804a000000 0x0001ff0000000000 0x050007c01f000000

def z101 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e07c03f9fc 0xf08000000008739c

def z102 : W := mkw 0x271400924e280150 0x082f800fa01a81c0 0xfffe00007c1c001c 0x0a0f803fe00b8180

def z103 : W := mkw 0x0a52459876b6aa45 0x20468dc0ca1bb94a 0x3e0e1c007c1c381c 0x100285c2ec0bb18c

def z104 : W := mkw 0x802000d142400080 0x0a8f802900bc8220 0xc1f000fffffc01e3 0x0aaf803d00ff8260

def z105 : W := mkw 0x440028fefb93f128 0x86c0412000fdfe94 0x000000fffffffffc 0xf0c0000000ffff9c

def z106 : W := mkw 0x2100000000000000 0x080f9e4f20000000 0xfffe000000000000 0x0e0fffffe0000000

def z107 : W := mkw 0xa73400ff7ffba1d0 0x0eefdf6fa0ffffe0 0xfffe00ffffffffff 0x0eefffffe0ffffe0

def z108 : W := mkw 0x863400d34e6801d0 0x02a0002080be83e0 0x000000fffffc01ff 0x00a0000000ff83e0

def z109 : W := mkw 0xa73400030c6801d0 0x02a0002fa08203e0 0xfffe0000000001ff 0x0220003fe00003e0

def z110 : W := mkw 0x0080800000000000 0x080fbe5911000000 0xc1f1e30000000000 0x0f0ffffd13000000

def z111 : W := mkw 0x000000fc63132000 0x0c4fde40007cd400 0x000000fffffc0000 0x088ff80000ff8000

def z112 : W := mkw 0x000000ac3193a000 0x04465f4000597c00 0x000000fffc03fe00 0x0cce7fc000f87c00

def z113 : W := mkw 0xa73400934e6801d0 0x02a6802fa09a83e0 0xfffe00007c1c01ff 0x0222803fe00b83e0

def z114 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xc1fe030000000000 0x010dfbfde3000000

def z115 : W := mkw 0xff776dfbfeeedbfd 0xaeafedbffefffbfe 0xffffffffffffffff 0xffffffffffffffff

def z116 : W := mkw 0xb5ad90d34a480190 0x0bafbe7f35bc82a0 0xc000001f80000000 0x000c783c00f00000

def z117 : W := mkw 0x0842450010848a05 0x200001804a01280a 0x00001c0000003800 0x100005c00c00300c

def z118 : W := mkw 0xa3340051466800d0 0x082f800fa0268160 0xfffe000003fc0003 0x0a2f803fe0078060

def z119 : W := mkw 0x008080fc7393a000 0x0c4fff59117dfc00 0xc1f1e3fffffffe00 0x0fcffffd13fffc00

def z120 : W := mkw 0x561128aaac225168 0x86866c3694da53d4 0xfffffcfffffff9ff 0xfeaffc3ffcfff3fc

def z121 : W := mkw 0xa73400d35ee881d0 0x0aaf812fa0bfabe0 0xfffe00ffffffffff 0x0eef87ffe0ffffe0

def z122 : W := mkw 0x39c9d00000000000 0x0100209f7f000000 0xffffff0000000000 0x0300003fff000000

def z123 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xffffe3ffffffc7ff 0xefff823ff3ffcff3

def z124 : W := mkw 0x440028aaa8025128 0x8680402000d85294 0x000000fffc03f9fc 0xf080000000f8739c

def z125 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x3ffe03e07ffc07ff 0x0bf383c3e30f8fe3

def z126 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x01ffe3e003ffc7e3 0xeff183c1f307ce73

def z127 : W := mkw 0x0000008000000000 0x0006000000180000 0x000000fffc000000 0x088e000000f80000

def z128 : W := mkw 0x0400000208000100 0x0280002600800280 0xfe000000000001fc 0x0200003e00000380

def z129 : W := mkw 0xa334005557f9a0d0 0x08699349a027ad60 0x01fe000003fc0603 0x006183c1e0078c60

def z130 : W := mkw 0x3109100000000000 0x01068c4624000000 0x0000000000000000 0x0000000000000000

def z131 : W := mkw 0x2500008208000100 0x0a8f802f20980280 0xfffe00fffc0001fc 0x0a8f803fe0f80380

def z132 : W := mkw 0x540128aaa8025128 0x86864c2604d85294 0x3e001cfffc03f9fc 0xf08204020cf8739c

def z133 : W := mkw 0xa3340051466800d0 0x0aa98029a0a68360 0xc1fe00ff83fc01e3 0x0aad803de0f78260

def z134 : W := mkw 0x4080a2fcf393e422 0x4c4fff50117dfc11 0x0001e3fffffffe00 0xeddfffc013fffc13

def z135 : W := mkw 0x5401280288005128 0x8280203614800294 0xfe01fc00000001fc 0xf200003e1c00039c

def z136 : W := mkw 0x5001282cb193f028 0x84407f5014417c14 0x0001fc000003fe00 0xf4407fc01c007c1c

def z137 : W := mkw 0xe7b4a2d3ce6845f2 0x4aafa03fb1be83f1 0xffffe3fffffc01ff 0xebbf803ff3ff83f3

def z138 : W := mkw 0x1849500000000000 0x01000cc04e000000 0x00001c0000000000 0x000005c00c000000

def z139 : W := mkw 0x0000002820020000 0x04004c0000405000 0x000000000003f800 0x04007c0000007000

def z140 : W := mkw 0x0000000010808000 0x0000010000012800 0x01f1e3e07fffffe3 0xeff387c1130ffe73

def z141 : W := mkw 0x084040fc7393a000 0x0c4fdfc04a7dfc00 0x3ffffffffffffe00 0x0fcfffc3fffffc00

def z142 : W := mkw 0xfffdf8fbee6a51f8 0x8faffefffffed3f4 0xfffffffffffff9ff 0xffaffffffffff3fc

def z143 : W := mkw 0x1001000000000000 0x0000201614000000 0xfe01fc0000000000 0x0200003e1c000000

def z144 : W := mkw 0xc0a0a26db1d3e4a2 0x4ec97f7911e57e31 0xc1f1e3ff83e3ffe3 0xeffd7ffd13f47e73

def z145 : W := mkw 0xc02022fdf3d3e4a2 0x46c0412000fdfe31 0x000000ffffffffe3 0xe0f0000000fffe73

def z146 : W := mkw 0x5c4168aaa8025128 0x86866cb65ed85294 0xfffffffffc03f9fc 0xff8ffffffff8739c

def z147 : W := mkw 0x440028fefb93f128 0x8ecfdf6000fdfe94 0x000000fffffffffc 0xfccfffc000ffff9c

def z148 : W := mkw 0x5001202080004020 0x06866c3614c04210 0xfe01fcff8003c1e0 0xee8e7c3e1cf04210

def z149 : W := mkw 0xc0a0a201804044a2 0x4a89323911800231 0xc1f1e300000001e3 0xef3d7a3d13000273

def z150 : W := mkw 0x210000fc7393a000 0x0c4fdf4f207dfc00 0xfffe00fffffffe00 0x0ecfffffe0fffc00

def z151 : W := mkw 0x000000745391a000 0x0c49d3400065ec00 0x000000ff83ffc600 0x0ccdfbc000f7cc00

def z152 : W := mkw 0x3dc9d88a28021108 0x890fbedf7f181084 0xffffff007c00381c 0x1f0fffffff08318c

def z153 : W := mkw 0x0000009862122000 0x00468c4000189000 0x0000000000000000 0x0000000000000000

def z154 : W := mkw 0xa52400ff7bdba190 0x0eefdf6f20fdfea0 0xc00000fffffffe00 0x0ccffffc00fffc00

def z155 : W := mkw 0xbffdd0d34e6801d0 0x0bafbeffffbe83e0 0xfffffffffffc01ff 0x0fafffffffff83e0

def z156 : W := mkw 0x271400fe7fbba150 0x0c6fdf46a07ffdc0 0x3e0e00fffffffe1c 0x0ccfffc2e0fffd80

def z157 : W := mkw 0x0000000000000000 0x0000000000000000 0x01f1e300000001e3 0xe330000113000273

def z158 : W := mkw 0xe7b4a2678d6945f2 0x4ea9723fb1e647f1 0xffffe3ff83e3c7ff 0xeffd7a3ff3f44ff3

def z159 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xfff1ffffffe3ffff 0xffff7e3f1ffc7fff

def z160 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffffe003e3c7e3 0xefffffffff044e73

def z161 : W := mkw 0x140108fe7b93b108 0x8c4fdf46047dfc84 0x3e001cfffffffe1c 0x1ccfffc20cfffd8c

def z162 : W := mkw 0x39c9d0fc7393a000 0x0d4fffdf7f7dfc00 0xfffffffffffffe00 0x0fcffffffffffc00

def z163 : W := mkw 0x0000000000000000 0x0000201010000000 0xc001e00000000000 0x0e0c783c10000000

def z164 : W := mkw 0x2100000000000000 0x080f800f20000000 0xfffe000000000000 0x0a0f803fe0000000

def z165 : W := mkw 0xf9e9f201804044a2 0x438020bf7f800231 0xffffff00000001e3 0xe330003fff000273

def z166 : W := mkw 0xd4a1aaefa94355aa 0xce8f7e3f15fc56b5 0xfff1ffffffe3ffff 0xffff7e3f1ffc7fff

def z167 : W := mkw 0x0842450010848a05 0x200001804a01280a 0x01f1ffe003e3ffe3 0xfff107c11f047e7f

def z168 : W := mkw 0xf73528fbee6a51f8 0x8eafec3fb4fed3f4 0xfffffcfffffff9ff 0xfeaffc3ffcfff3fc

def z169 : W := mkw 0xc0202265814144a2 0x4e89402900e44631 0xc1f000ff83e3c7e3 0xeafd003d00f44e73

def z170 : W := mkw 0x0210000004200040 0x0000000080020140 0x3ffffce07ffff9ff 0xfea38403fc0ff3fc

def z171 : W := mkw 0x0a5245a834a68a45 0x24064d80ca5b794a 0x3fffffffffffffff 0xffffffc3ffffffff

def z172 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f1e31f80000000 0x0f0d7a3d13f00000

def z173 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe0000fffc0001fc 0x0a8e783e00f80380

def z174 : W := mkw 0x8e7645d35eec8bd5 0x22a001a0cabfabea 0x3fffffffffffffff 0xfff387c3ffffffff

def z175 : W := mkw 0x3949500000000000 0x0106acd67e000000 0xfe0ffc0000000000 0x0e0efdfefc000000

def z176 : W := mkw 0x56132daabca6db6d 0xa6866d3694db7bde 0xfe01fcffffffffff 0xfefe7c3e1cffffff

def z177 : W := mkw 0x58436d28b086da2d 0xa4006d905e41781e 0x0001ff000003fe00 0xf5507fc01f007c1f

def z178 : W := mkw 0x5e536daabca6db6d 0xa6866db6dedb7bde 0xffffffffffffffff 0xffffffffffffffff

def z179 : W := mkw 0x021205fc77b7aa45 0x24404100807ffd4a 0x000000ffffffffff 0xf0f0000000ffffff

def z180 : W := mkw 0xa33400d1466800d0 0x082f8009a03e8160 0x01fe00fffffc0003 0x08af8001e0ff8060

def z181 : W := mkw 0x0000000000000000 0x0000000000000000 0x3e01fc0000000000 0x0e0204021c000000

def z182 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x0000001f83fc0600 0x004dfbc000f78c00

def z183 : W := mkw 0x18c9d00000000000 0x01003ed05f000000 0x3fffff0000000000 0x0f03ffc3ff000000

def z184 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x0001ffe07fffffff 0xf5f007c01f0fffff

def z185 : W := mkw 0xbffdd0030c6801d0 0x03a020bfff8203e0 0xffffff00000001ff 0x0320003fff0003e0

def z186 : W := mkw 0xfffdf2f7cf6945f2 0x4faffefffffec7f1 0xffffffffffffc7ff 0xefffffffffffcff3

def z187 : W := mkw 0xf9e9f265814144a2 0x4f8ffeff7fe44631 0xffffffff83e3c7e3 0xeffffffffff44e73

def z188 : W := mkw 0xa73400d34e6801d0 0x082f800fa03e81e0 0x3ffe00007ffc001f 0x00238003e00f81e0

def z189 : W := mkw 0x3949500000000000 0x090f8ccf6e000000 0xfffe1c0000000000 0x0a0f85ffec000000

def z190 : W := mkw 0x040000aa28020100 0x06864c2600d85280 0xfe0000fffc03f9fc 0x0e8e7c3e00f87380

def z191 : W := mkw 0x0a52452c35b7aa45 0x24405fc0ca437d4a 0x3fffffe07fffffff 0xfff3ffc3ff0fffff

def z192 : W := mkw 0x80a0826501410482 0x4c09520901644421 0x01f003ff83e3c603 0x0dfd7a0103f44c63

def z193 : W := mkw 0x1841400000000000 0x00062c965e000000 0xffffff0000000000 0x0f0fffffff000000

def z194 : W := mkw 0x46122daabca6db6d 0xa680412080db7bde 0x000000ffffffffff 0xf0f0000000ffffff

def z195 : W := mkw 0x000000545391a000 0x084993400025ac00 0x0000000003fc0600 0x004183c000078c00

def z196 : W := mkw 0xc0a0a241804044a2 0x4a89203911a40231 0xc1f1e3ff83e001e3 0xebbd003d13f40273

def z197 : W := mkw 0x7589b8aaa8025128 0x8f8ffe7f35d85294 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z198 : W := mkw 0xd4212aefa94355aa 0xc6866c3614fc56b5 0xfe01fcffffe3ffff 0xfefe7c3e1cfc7fff

def z199 : W := mkw 0x5c436daab886db2d 0xa6866db65ed97a9e 0xfe01fffffc03fffc 0xffde7ffe1ff87f9f

def z200 : W := mkw 0x8020004100400080 0x0a89002900a40220 0xc1f000ff83e001e3 0x0aad003d00f40260

def z201 : W := mkw 0x540128feeb137128 0x8ecffe7614fcd694 0xc000001f80000000 0x000c783c00f00000

def z202 : W := mkw 0x040000d24a000100 0x0a8f802600bc8280 0xfe0000fffffc01fc 0x0a8f803e00ff8380

def z203 : W := mkw 0x39c9d0d042000000 0x090fbedf7f3c8000 0xfffffffffffc0000 0x0f8fffffffff8000

def z204 : W := mkw 0xc0202265814144a2 0x4680402000e44631 0x01f1e3ff83e3c7e3 0xeff1020113f44e73

def z205 : W := mkw 0x000000545391a000 0x084993400025ac00 0x000000e07ffffe00 0x0cc387c0000ffc00

def z206 : W := mkw 0x021000fc77b3a040 0x0c4fdf40807ffd40 0x3ffe00ffffffffff 0x0eefffc3e0ffffe0

def z207 : W := mkw 0x8020004100400080 0x0a89002900a40220 0xc1f1e3ff83e3c7e3 0xeffd023d13f44e73

def z208 : W := mkw 0x2940400000000000 0x080f808f6a000000 0xffffff0000000000 0x0f0f87ffff000000

def z209 : W := mkw 0xbf7d50d34e6801d0 0x0baf8cefeebe83e0 0xfffe1cfffffc01ff 0x0aaf85ffecff83e0

def z210 : W := mkw 0x000000105290a000 0x004081400001a800 0x00000000001c0000 0x000081c000038000

def z211 : W := mkw 0x0000000000000000 0x00001e4000000000 0x0000000000000000 0x04007fc000000000

def z212 : W := mkw 0x2310000004200040 0x080f800fa0020140 0xfffe00e07ffc01ff 0x0aaf803fe00f83e0

def z213 : W := mkw 0x000000a820020000 0x04064c0000585000 0x3e01fcfffc03f9fc 0xfe8e7c021cf8739c

def z214 : W := mkw 0x000000a820020000 0x0400400000585000 0x000000fffc03f800 0x0080000000f87000

def z215 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x01fe03e07ffffe03 0x0df387c1e30ffc63

def z216 : W := mkw 0x0212050014a48a45 0x200001008003294a 0x000000e07fffffff 0xf0f00000000fffff

def z217 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x0000001f8003fe00 0x044c7fc000f07c00

def z218 : W := mkw 0x18c9d00000000000 0x01003ed05f000000 0x0001ff0000000000 0x05007fc01f000000

def z219 : W := mkw 0x18c9d00000000000 0x01063ed65f000000 0xfe01ff0000000000 0x0f0e7ffe1f000000

def z220 : W := mkw 0x0000005443112000 0x0849924000248400 0x0000000000000000 0x0000000000000000

def z221 : W := mkw 0xfbfbf76595e5cee7 0x6f8fffffffe76f7b 0xffffffffffffffff 0xffffffffffffffff

def z222 : W := mkw 0xf52528fbea4a51b8 0x8eafec3f34fcd2b4 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z223 : W := mkw 0x863400ff7ffba1d0 0x0eefdf6080ffffe0 0x000000ffffffffff 0x0cefffc000ffffe0

def z224 : W := mkw 0x5401280288005128 0x8280203614800294 0xfe01fce07c03f9fc 0xfe82043e1c08739c

def z225 : W := mkw 0x2100000000000000 0x0809800920000000 0x01fe000000000000 0x00018001e0000000

def z226 : W := mkw 0xa52400d34a480190 0x0aaf802f20bc82a0 0xc000001f80000000 0x000c003c00f00000

def z227 : W := mkw 0x000000d042000000 0x080f8000003c8000 0x0000001f80000000 0x000c000000f00000

def z228 : W := mkw 0x0000000000000000 0x080f9e4000000000 0x0000000000000000 0x0c0fffc000000000

def z229 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffffe07c03f9fc 0xff8fffffff08739c

def z230 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x01fe030003fc0603 0x017183c1e3078c63

def z231 : W := mkw 0x000000a830828000 0x04064d0000597800 0x000000fffffffe00 0x0ccfffc000fffc00

def z232 : W := mkw 0x4000206481014020 0x0e89723010e44610 0xc001e0ff83e3c7e0 0xeecd7a3c10f44e10

def z233 : W := mkw 0x4080a22cb193e422 0x44407f5011417c11 0x0001e3000003fe00 0xe5507fc013007c13

def z234 : W := mkw 0x4e526daabca6db6d 0xa68041a0cadb7bde 0x3fffffffffffffff 0xfff387c3ffffffff

def z235 : W := mkw 0xe73422f7cf6945f2 0x4eafc02fa0fec7f1 0xfffe00ffffffc7ff 0xeaff803fe0ffcff3

def z236 : W := mkw 0xc0a0a26591c1c4a2 0x4e89733911e56e31 0xc1f1e3ffffffffe3 0xeffffffd13fffe73

def z237 : W := mkw 0x1001000000000000 0x00062c1614000000 0xc000000000000000 0x000c783c00000000

def z238 : W := mkw 0x061400924e280150 0x00200000801a81c0 0x000000007c1c001c 0x00000000000b8180

def z239 : W := mkw 0x2f5645925eac8b55 0x20268186ea1ba9ca 0x3fffffe07fffffff 0xfff387c3ff0fffff

def z240 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x3fffff007c1c39ff 0xf33285c3ff0bb3ff

def z241 : W := mkw 0x0080800000000000 0x0000321011000000 0x0001e30000000000 0x05007a0013000000

def z242 : W := mkw 0x8020004100400080 0x0280002000a40220 0x000000ff83e001e3 0x00a0000000f40260

def z243 : W := mkw 0xa524000308480190 0x02a0002f208002a0 0xc000000000000000 0x0000003c00000000

def z244 : W := mkw 0x0840400000000000 0x000000804a000000 0x3fffffe07c03f9fc 0xff8387c3ff08739c

def z245 : W := mkw 0xc2b2a76595e5cee7 0x6e89733991e76f7b 0xc1f1e3ffffffffff 0xfffd7a3d13ffffff

def z246 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x0000001ffc1c3800 0x000efdc000fbb000

def z247 : W := mkw 0xe3b4a275c76944f2 0x4ea9f239b1e6c771 0xc1ffe3ff83ffc7e3 0xeffdfa3df3f7ce73

def z248 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xc00000fffc03f9fc 0xf08c783c00f8739c

def z249 : W := mkw 0x2100000000000000 0x080f800f20000000 0xc000000000000000 0x000c003c00000000

def z250 : W := mkw 0x80a0824501410482 0x4809120901240421 0x01f1e3e003e3c7e3 0xeff1020113044e73

def z251 : W := mkw 0x4000202080004020 0x0680603010c04210 0xc001e0ff8003c1e0 0xee8c783c10f04210

def z252 : W := mkw 0x3949500000000000 0x090f9ec66e000000 0x3e0e1c0000000000 0x0c0fffc2ec000000

def z253 : W := mkw 0x58c9f828a0025028 0x85007ed05f405014 0x0001ff000003f800 0xf5007fc01f00701c

def z254 : W := mkw 0x39c9d00000000000 0x0909bed97f000000 0x01ffff0000000000 0x0501ffc1ff000000

def z255 : W := mkw 0xc0a0a2eda14344a2 0x4e8f7e3911fc5631 0xc1f1e3ffffe3ffe3 0xefff7e3d13fc7e73

def z256 : W := mkw 0x5e536d028c245b6d 0xa28020b6de8203de 0xffffff00000001ff 0xf330003fff0003ff

def z257 : W := mkw 0x3189900000000000 0x090fbe5f35000000 0xfffe000000000000 0x0a0ff83fe0000000

def z258 : W := mkw 0xe73420f3ce6841f0 0x0eafe03fb0fec3f0 0xffffe0ffffffc1ff 0xeeaff83ff0ffc3f0

def z259 : W := mkw 0xcaf2e7fdf7f7eee7 0x6ecffff9dbffff7b 0xffffffffffffffff 0xffffffffffffffff

def z260 : W := mkw 0x2f5645925eac8b55 0x20268186ea1ba9ca 0x3e0e1c007c1c381c 0x100285c2ec0bb18c

def z261 : W := mkw 0x08c8d00000000000 0x010012c04b000000 0x0000030000000000 0x010003c003000000

def z262 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x3fffff007c1c381c 0x1f0387c3ff0bb18c

def z263 : W := mkw 0x4080a26481014422 0x4c09721011644411 0x0001e3ff83e3c600 0xeddd7a0013f44c13

def z264 : W := mkw 0x4000202080004020 0x0680603010c04210 0xc000001f80000000 0x000c783c00f00000

def z265 : W := mkw 0x0400008208000100 0x0286002600980280 0xfe01fcfffc03f9fc 0xfe8e043e1cf8739c

def z266 : W := mkw 0xaffcd0d34e6801d0 0x0baf92efebbe83e0 0xfffe03fffffc01ff 0x0baf83ffe3ff83e0

def z267 : W := mkw 0x0000000010808000 0x0000010000012800 0x000000e07ffffe00 0x00c00000000ffc00

def z268 : W := mkw 0x540128faea025128 0x8e8fec3614fcd294 0xfe01fcfffffff9fc 0xfe8ffc3e1cfff39c

def z269 : W := mkw 0x0212050014a48a45 0x200001008003294a 0x000000007c1c381c 0x10000000000bb18c

def z270 : W := mkw 0x4000222481014422 0x4400400000404411 0x000000000003c600 0xe050000000004c13

def z271 : W := mkw 0xa120004100400080 0x0a8f802f20a40220 0xfffe00ff83e001e3 0x0aaf803fe0f40260

def z272 : W := mkw 0xf7b5aaffef6b55fa 0xceaffe3fb5fed7f5 0xffffffffffffffff 0xfffffe3fffffffff

def z273 : W := mkw 0x80a082fd73d3a482 0x4c4fdf49017dfc21 0x01f003fffffffe03 0x0dffffc103fffc63

def z274 : W := mkw 0x29c8d0545391a000 0x094993c96b25ac00 0x01fe030003fc0600 0x014183c1e3078c00

def z275 : W := mkw 0x3189900000000000 0x090fbe5f35000000 0xc1f1e30000000000 0x0f0d7a3d13000000

def z276 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xfe0e1c0000000000 0x000efdfeec000000

def z277 : W := mkw 0xb9e9d24501410482 0x490fbedf7f240421 0xffffff0003e00603 0x0f7fffffff040c63

def z278 : W := mkw 0x802000fd73d3a080 0x0ecfdf6900fdfe20 0xc1f000ffffffffe3 0x0eeffffd00fffe60

def z279 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x3fffff0003fc07ff 0xf37183c3ff078fff

def z280 : W := mkw 0xf73528fffffbf1f8 0x8eefff7fb4fffff4 0xfffffcffffffffff 0xfeeffffffcfffffc

def z281 : W := mkw 0x29c8d00000000000 0x090f9ec96b000000 0x01fe030000000000 0x0d0fffc1e3000000

def z282 : W := mkw 0x0a52459876b6aa45 0x20468dc0ca1bb94a 0x3fffffe07fffffff 0xfff387c3ff0fffff

def z283 : W := mkw 0x0212050014a48a45 0x200001008003294a 0x3e01fce07fffffff 0xfef204021c0fffff

def z284 : W := mkw 0x2948500000000000 0x010080c06a000000 0x000e000000000000 0x000081c0e0000000

def z285 : W := mkw 0x440028aaa8025128 0x8680603010d85294 0xc001e0fffc03f9fc 0xfe8c783c10f8739c

def z286 : W := mkw 0x18c9d00000000000 0x09093ed95f000000 0xc1f1ff0000000000 0x0f0d7ffd1f000000

def z287 : W := mkw 0xc0a0a221804044a2 0x4680603911c04231 0xc1f1e3ff8003c1e3 0xefbc783d13f04273

def z288 : W := mkw 0x5cc9f8aaa8025128 0x87867ef65fd85294 0xfe01fffffc03f9fc 0xff8e7ffe1ff8739c

def z289 : W := mkw 0x771528baee2a5178 0x86a6ec36b4dad3d4 0xfe0ffcfffc1ff9fc 0xfe8efc3efcfbf39c

def z290 : W := mkw 0xcaf2e76595e5cee7 0x6e8973b9dbe76f7b 0xc1ffe3ff83ffc7e3 0xeffdfbfdf3f7ce73

def z291 : W := mkw 0x000000f862020000 0x0c0fcc00007cd000 0x000000fffffff800 0x0c8ffc0000fff000

def z292 : W := mkw 0x50012828a0025028 0x84006c1014405014 0x3e01fce07c03f9fc 0xfe827c021c08739c

def z293 : W := mkw 0x4000202080004020 0x0400601010404010 0x0001e0000003c000 0xe400780010004010

def z294 : W := mkw 0x39c9d00000000000 0x01003edf7f000000 0xffffff0000000000 0x07007fffff000000

def z295 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xc001ff0000000000 0x050c7ffc1f000000

def z296 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e003e3c600 0x0cc1020000044c00

def z297 : W := mkw 0x39c9d02c3193a000 0x0d4fffdf7f417c00 0xffffff000003fe00 0x0f4fffffff007c00

def z298 : W := mkw 0x000000083092a000 0x00400d4000013800 0x0000000000003800 0x000005c000003000

def z299 : W := mkw 0x4080a22481014422 0x4400721011404411 0x0000000000000000 0x0000780000000000

def z300 : W := mkw 0x0000002401010000 0x0400520000404400 0x000000000003c600 0x04407a0000004c00

def z301 : W := mkw 0x540128bafa92f128 0x86c6ed7614d9fa94 0xfe01fcfffc1ff9fc 0xfe8efdfe1cfbf39c

def z302 : W := mkw 0xc232276595e5cee7 0x6680412080e76f7b 0x000000ffffffffff 0xf0f0000000ffffff

def z303 : W := mkw 0x80a0824501410482 0x4809321911240421 0xc1f1e30003e00603 0x0f7d7a3d13040c63

def z304 : W := mkw 0x0a50400004200040 0x00000080ca020140 0x3fffffe07ffc01ff 0x0fa387c3ff0f83e0

def z305 : W := mkw 0x863400030c6801d0 0x02a00020808203e0 0x00000000000001ff 0x00200000000003e0

def z306 : W := mkw 0x3bdbd50014a48a45 0x2100219fff03294a 0xffffffe07fffffff 0xfff387ffff0fffff

def z307 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001e0e00003c1e0 0xee80000010004210

def z308 : W := mkw 0xdef3efefbde7dfef 0xee8f7fbfdfff7fff 0xffffffffffffffff 0xffffffffffffffff

def z309 : W := mkw 0xc0a0a265814144a2 0x4c09721911644431 0x01f1e30003e3c603 0xe5717a0113044c73

def z310 : W := mkw 0x0210000004200040 0x0000000080020140 0x000000e07ffc01ff 0x00a00000000f83e0

def z311 : W := mkw 0x18c9d0fc7393a000 0x0d4fffd05f7dfc00 0x0001fffffffffe00 0x0dcfffc01ffffc00

def z312 : W := mkw 0x0212050014a48a45 0x200001008003294a 0x01f1e3e07fffffff 0xfff10201130fffff

def z313 : W := mkw 0xb73500d34e6801d0 0x0aafac3fb4be83e0 0xfffffcfffffc01ff 0x0eaffc3ffcff83e0

def z314 : W := mkw 0x80a0824501410482 0x4a89122901a40621 0xc1f003ff83e007e3 0x0bfd023d03f40e63

def z315 : W := mkw 0xc4202aefa94355aa 0xc680402000fc56b5 0x000000ffffe3ffff 0xf0f0000000fc7fff

def z316 : W := mkw 0xc0a0a245814144a2 0x4a89323911a40631 0xc1f1e30003e007e3 0xe371023d13040e73

def z317 : W := mkw 0xa73400d75ff9a1d0 0x0aef936fa0bfafe0 0xfffe00fffffc07ff 0x0aef83ffe0ff8fe0

def z318 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe001c1ffc00381c 0x100e7c3e0cf8318c

def z319 : W := mkw 0x82300041046000c0 0x0a89002980a60360 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z320 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x3ffe1ce07ffc39ff 0x1aa385c3ec0fb3ec

def z321 : W := mkw 0x3b5b550014a48a45 0x21068dc6ee03294a 0x3fffffe07fffffff 0xfff387c3ff0fffff

def z322 : W := mkw 0x000000dc7393a000 0x084f9f40003dbc00 0x000000007ffc3e00 0x004387c0000fbc00

def z323 : W := mkw 0x000000987292a000 0x00468d400019b800 0x000000007c1c3800 0x000285c0000bb000

def z324 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0c0387c000000000

def z325 : W := mkw 0x39c9d0545391a000 0x094fbfdf7f25ac00 0xffffff0003fc0600 0x0f4fffffff078c00

def z326 : W := mkw 0x000000d042000000 0x080f9e40003c8000 0x000000fffffc0000 0x0c8fffc000ff8000

def z327 : W := mkw 0x0840400000000000 0x080f9ec04a000000 0x3fffff0000000000 0x0f0fffc3ff000000

def z328 : W := mkw 0x0000000010808000 0x0000010000012800 0x3e01fce07ffffffc 0xfec387c21c0fff9c

def z329 : W := mkw 0x1401088a28021108 0x80062c1614181084 0xfe01fc007c00381c 0x1e0e7c3e1c08318c

def z330 : W := mkw 0x0000000000000000 0x00068c4000000000 0x0000000000000000 0x000285c000000000

def z331 : W := mkw 0x863605d35eec8bd5 0x22a0012080bfabea 0x000000ffffffffff 0xf0f0000000ffffff

def z332 : W := mkw 0x000000987292a000 0x084f9f400019b800 0x000000007c1c3800 0x0c0fffc0000bb000

def z333 : W := mkw 0xa33400fd77fba0d0 0x0c6fdf49a07ffd60 0x01fe00fffffffe03 0x0cefffc1e0fffc60

def z334 : W := mkw 0x3949500000000000 0x010000866e000000 0x3e0e1c0000000000 0x00000002ec000000

def z335 : W := mkw 0x1e534d8a3ca69b4d 0xa0060d86ce1b39ce 0x3e0e1c007c1c381c 0x100285c2ec0bb18c

def z336 : W := mkw 0x0000000000000000 0x0000000000000000 0x01f0030003e00603 0x0171020103040c63

def z337 : W := mkw 0x2100000000000000 0x0006800620000000 0x3e0e000000000000 0x00028002e0000000

def z338 : W := mkw 0x0000000000000000 0x0280002000800200 0xc00000ff800001e0 0x0a8c003c00f00200

def z339 : W := mkw 0x1081800000000000 0x080f3e1f15000000 0xfff1ff0000000000 0x0f0f7e3f1f000000

def z340 : W := mkw 0xaf7645d34e6c0bd5 0x2aaf80afeabe83ea 0xfffffffffffc01ff 0xfbbf803fffff83ff

def z341 : W := mkw 0x39c9d06401010000 0x0d0ffedf7f644400 0xffffffff83e3c600 0x0fcffffffff44c00

def z342 : W := mkw 0x0a5245fc77b7aa45 0x2c4fdfc0ca7ffd4a 0x01fe03fffffffe03 0x0dffffc1e3fffc63

def z343 : W := mkw 0xaf7645d35eec8bd5 0x2aaf81afeabfabea 0xfffe1cfffffc39ff 0x1aaf85ffecffb3ec

def z344 : W := mkw 0xa3340051466800d0 0x08298009a0268160 0x3ffe00e07ffc01ff 0x0aa38003e00f83e0

def z345 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe01fc1f800001fc 0xf20c783e1cf0039c

def z346 : W := mkw 0xc0a0a201804044a2 0x4280203911800231 0xc000000000000000 0x0000003c00000000

def z347 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc00000ff83e3c600 0x0ccd7a3c00f44c00

def z348 : W := mkw 0x0a52450004240a45 0x20000080ca02014a 0x3fffff00000001ff 0xff3387c3ff0003ff

def z349 : W := mkw 0x80a0820100400482 0x4000000901000021 0x01f0030000000003 0x0130000103000063

def z350 : W := mkw 0x2714009a7ebaa150 0x00668d46a01bb9c0 0x3e0e00007c1c381c 0x000285c2e00bb180

def z351 : W := mkw 0x1001000000000000 0x00062c1614000000 0xfe01fce07c03f9fc 0xfe8e7c3e1c08739c

def z352 : W := mkw 0x440028aaa8025128 0x8680402000d85294 0x3e01fcfffc03f9fc 0xfe8204021cf8739c

def z353 : W := mkw 0xc02022fdf3d3e4a2 0x4ecfdf6000fdfe31 0x000000ffffffffe3 0xecffffc000fffe73

def z354 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x01ffff0003fffe03 0xf57187c1ff07fc7f

def z355 : W := mkw 0x0842450010848a05 0x200001804a01280a 0x3e01ffe07c03fffc 0xffd207c21f087f9f

def z356 : W := mkw 0x0212050004240a45 0x200000008002014a 0x00000000000001ff 0xf0300000000003ff

def z357 : W := mkw 0xd4a1aa67894155aa 0xce89723f15e446b5 0xfff1ffff83e3c7ff 0xfffd7a3f1ff44fff

def z358 : W := mkw 0x08c0c00000000000 0x080932995b000000 0xffffff0000000000 0x0f0fffffff000000

def z359 : W := mkw 0x4080a22481014422 0x4680723011c04611 0xc001e3ff8003c7e0 0xefdc7a3c13f04e13

def z360 : W := mkw 0x39c9d0fc63132000 0x0d4ffedf7f7cd400 0xffffff1f80000000 0x0f0ffffffff00000

def z361 : W := mkw 0xbffdd0ff7ffba1d0 0x0fefffffffffffe0 0xffffffffffffffff 0x0fefffffffffffe0

def z362 : W := mkw 0x4080a22481014422 0x4c09721911404411 0xc1f1e3000003c600 0xef5d7a3d13004c13

def z363 : W := mkw 0x0212050014a48a45 0x200001008003294a 0x000000e07fffffff 0xfcf387c0000fffff

def z364 : W := mkw 0x318990fc7393a000 0x0d4fff5f357dfc00 0xc00000fffffffe00 0x0ccffffc00fffc00

def z365 : W := mkw 0x4000202080004020 0x0680603010c04210 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z366 : W := mkw 0x50012828a0025028 0x86806c3014c05214 0xc001fcff8003f9e0 0xfe8c7c3c1cf0721c

def z367 : W := mkw 0x7dc9f80288005128 0x838020bf7f800294 0xffffff00000001fc 0xf300003fff00039c

def z368 : W := mkw 0xcaf2e70184644ee7 0x628020b9db82037b 0xffffff00000001ff 0xf330003fff0003ff

def z369 : W := mkw 0x5081aa2ca103542a 0xc4007e1015405415 0x0001ff000003fe00 0xf5507e001f007c1f

def z370 : W := mkw 0x39c9d00000000000 0x0106bed67f000000 0x3e0fff0000000000 0x0502ffc2ff000000

def z371 : W := mkw 0x8020006501410080 0x0e89522900e44620 0xc1f000ff83e3c7e3 0x0eed7a3d00f44e60

def z372 : W := mkw 0x29c8d00000000000 0x090992c96b000000 0x3fffff0000000000 0x0f0387c3ff000000

def z373 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x01f1e3ffffffffe3 0xefffffc113fffe73

def z374 : W := mkw 0x0000002c3193a000 0x0440410000417c00 0x000000000003fe00 0x0040000000007c00

def z375 : W := mkw 0x842400d34a480190 0x02a0002000bc82a0 0x0000001f80000000 0x0000000000f00000

def z376 : W := mkw 0x3d49588a28021108 0x81068cc66e181084 0x3e0e1c007c00381c 0x100285c2ec08318c

def z377 : W := mkw 0xe5a4a2f7cb4945b2 0x4eaff23f31fcc6b1 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z378 : W := mkw 0x0000006401010000 0x0400400000644400 0x000000ff83e3c600 0x00c0000000f44c00

def z379 : W := mkw 0x4000202080004020 0x0680603010c04210 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z380 : W := mkw 0xaf7645d35eec8bd5 0x2aaf81afeabfabea 0xfffe03fffffc07ff 0x0bff83ffe3ff8fe3

def z381 : W := mkw 0x000000fc7393a000 0x0c495300007dfc00 0x000000fffffffe00 0x0ccd7a0000fffc00

def z382 : W := mkw 0x0a52450004240a45 0x20000080ca02014a 0x01fe030000000003 0x01300001e3000063

def z383 : W := mkw 0xd4a1aaefa94355aa 0xce8f7e3f15fc56b5 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z384 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x3fffff000003ffff 0xf77007c3ff007fff

def z385 : W := mkw 0x1001000000000000 0x00060c0604000000 0x3e001c0000000000 0x000204020c000000

def z386 : W := mkw 0x1adbd50014a48a45 0x21003fd0df03294a 0x3fffffe07fffffff 0xfff3ffc3ff0fffff

def z387 : W := mkw 0xc6b4a2f7cf6945f2 0x4ea9723991fec7f1 0xc1f1e3ffffffc7ff 0xeffd7a3d13ffcff3

def z388 : W := mkw 0x3101000000000000 0x080fac1f34000000 0xfffffc0000000000 0x0e0ffc3ffc000000

def z389 : W := mkw 0x1401089a7a92b108 0x80468d460419b884 0x3e001c007c1c381c 0x100285c20c0bb18c

def z390 : W := mkw 0xe7b4a2fffffbe5f2 0x4eefff7fb1fffff1 0xffffe3ffffffffff 0xeffffffff3fffff3

def z391 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x000000fffffffe00 0x00cc780000fffc00

def z392 : W := mkw 0xa73400db7efaa1d0 0x0aef8d6fa0bfbbe0 0xfffe00fffffc39ff 0x0aaf85ffe0ffb3e0

def z393 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f000ff83e001e3 0x0aad783d00f40260

def z394 : W := mkw 0x1a53450014a48a45 0x20062d96de03294a 0xffffffe07fffffff 0xffffffffff0fffff

def z395 : W := mkw 0x0000002000000000 0x0400400000404000 0x000000ff8003c000 0x0c8c780000f04000

def z396 : W := mkw 0x540128aaa8025128 0x86806c3014d85294 0x0001fcfffc03f9fc 0xf4807c001cf8739c

def z397 : W := mkw 0x8020004100400080 0x0809000900240020 0x01f0000003e00003 0x0021000100040060

def z398 : W := mkw 0x540128feeb137128 0x8ecffe7614fcd694 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z399 : W := mkw 0xa52400d34a480190 0x0aaf802f20bc82a0 0xfffe001f80000000 0x0a0f803fe0f00000

def z400 : W := mkw 0x1089900000000000 0x01003e5015000000 0x0000000000000000 0x0000780000000000

def z401 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001fc000003f800 0xf40004001c00701c

def z402 : W := mkw 0x0080800000000000 0x0809120901000000 0x01f0030000000000 0x0101020103000000

def z403 : W := mkw 0x3bdbd5fc77b7aa45 0x2d4fffdfff7ffd4a 0xffffffffffffffff 0xffffffffffffffff

def z404 : W := mkw 0x863400ff7ffba1d0 0x06e0412080ffffe0 0x000000ffffffffff 0x00e0000000ffffe0

def z405 : W := mkw 0x40002828a0025028 0x8400400000405014 0x000000000003f800 0xf00000000000701c

def z406 : W := mkw 0x5001280080005028 0x8000201014000014 0x0001fc0000000000 0xf00000001c00001c

def z407 : W := mkw 0x500128a8a0025028 0x84066c1014585014 0x0001fcfffc03f800 0xfc8e7c001cf8701c

def z408 : W := mkw 0x0000000000000000 0x0000000000000000 0x01f000e003e001e3 0x0aa1000100040260

def z409 : W := mkw 0x2b52450014a48a45 0x280f818fea03294a 0xffffffe07fffffff 0xffff87ffff0fffff

def z410 : W := mkw 0x0000000000000000 0x0000000000000000 0x3ffe000000000000 0x0a038003e0000000

def z411 : W := mkw 0x79c9f02080004020 0x0f8ffeff7fc04210 0xffffffff8003c1e0 0xef8ffffffff04210

def z412 : W := mkw 0x000000d87292a000 0x084f8d40003db800 0x000000fffffc3800 0x088f85c000ffb000

def z413 : W := mkw 0x2188900000000000 0x0909924921000000 0x0000000000000000 0x0000000000000000

def z414 : W := mkw 0xd63528fbee6a51f8 0x86a66c3694fed3f4 0xfe01fcfffffff9ff 0xfeae7c3e1cfff3fc

def z415 : W := mkw 0x000000f443010000 0x0c0fd200007cc400 0x000000ffffffc600 0x0ccffa0000ffcc00

def z416 : W := mkw 0xa9e8d24501410482 0x490992c96b240421 0x01fe030003e00603 0x017183c1e3040c63

def z417 : W := mkw 0x842000c308400180 0x0a8f002f00bc02a0 0xfff000ffffe001ff 0x0aaf003f00fc03e0

def z418 : W := mkw 0x000000041191a000 0x0040134000012c00 0x0000000000000600 0x004003c000000c00

def z419 : W := mkw 0x3f5d50924e280150 0x01268cc6ee1a81c0 0x3e0e1c007c1c001c 0x000285c2ec0b8180

def z420 : W := mkw 0xa73400830c6801d0 0x02a6002fa09a03e0 0xfffe00fffc0001ff 0x0aae003fe0f803e0

def z421 : W := mkw 0xe1a0a265814144a2 0x4e8ff23f31e44631 0xffffe3ff83e3c7e3 0xeffffa3ff3f44e73

def z422 : W := mkw 0xa73400430c6801d0 0x0aa9002fa0a603e0 0xfffe00ff83e001ff 0x0aad003fe0f403e0

def z423 : W := mkw 0xd4a1aaefa94355aa 0xce8f7e3f15fc56b5 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z424 : W := mkw 0x39c9d00010808000 0x090fbfdf7f012800 0xffffffe07ffffe00 0x0fcfffffff0ffc00

def z425 : W := mkw 0x0080800000000000 0x0000201911000000 0xc1f1e30000000000 0x0300003d13000000

def z426 : W := mkw 0x3bd9d00004200040 0x090fbedfff020140 0xffffffe07ffc01ff 0x0fafffffff0f83e0

def z427 : W := mkw 0x5e536daaac265b6d 0xa6866cb6deda53de 0xfffffffffc03f9ff 0xffbe7c3ffff873ff

def z428 : W := mkw 0xcaf2e70194e4cee7 0x628021b9db832b7b 0xffffffe07fffffff 0xfff387ffff0fffff

def z429 : W := mkw 0x000000fc63132000 0x0c4fde40007cd400 0x0000001f80000000 0x0c0fffc000f00000

def z430 : W := mkw 0xc2b0a265856144e2 0x4e89723991e64771 0xffffe3ffffffc7ff 0xeffffa3ff3ffcff3

def z431 : W := mkw 0xa73400ff7ffba1d0 0x0eefc12fa0ffffe0 0xfffe00ffffffffff 0x0aef803fe0ffffe0

def z432 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xc001e0ff8003c1e0 0xee8c783c10f04210

def z433 : W := mkw 0x000000fc7393a000 0x0c49d340007dfc00 0x000000fffffffe00 0x00c183c000fffc00

def z434 : W := mkw 0xa52400ff6b5b2190 0x0eefde6f20fcd6a0 0xc000001f80000000 0x000c783c00f00000

def z435 : W := mkw 0x0000006411818000 0x0c09530000656c00 0x000000fffffffe00 0x0ccfffc000fffc00

def z436 : W := mkw 0x39c9d0987292a000 0x094fbfdf7f19b800 0xffffff007c1c3800 0x0f0fffffff0bb000

def z437 : W := mkw 0x39c9d00000000000 0x0909329f7f000000 0xffffff0000000000 0x0f0d7a3fff000000

def z438 : W := mkw 0xc0202265814144a2 0x4680603010e44631 0xc001e0ff83e3c7e3 0xeefc783c10f44e73

def z439 : W := mkw 0x2180800000000000 0x080fb21f31000000 0xffffe30000000000 0x0f0ffa3ff3000000

def z440 : W := mkw 0x0840400000000000 0x000000804a000000 0x3fffff0000000000 0x03000003ff000000

def z441 : W := mkw 0x4000200080004020 0x0280203010800210 0xc001e000000001e0 0xe200003c10000210

def z442 : W := mkw 0x79c9f828a0025028 0x8d0ffedf7f405014 0xffffff000003f800 0xff0fffffff00701c

def z443 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e07c03f800 0x0c82040000087000

def z444 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfff1ffffffe3ffff 0xffff7e3f1ffc7fff

def z445 : W := mkw 0x1401008208000100 0x02862c3614980280 0xfe01fcfffc0001fc 0x0e8e7c3e1cf80380

def z446 : W := mkw 0x0840400010808000 0x000001804a012800 0x3fffffe07ffffe00 0x0fc387c3ff0ffc00

def z447 : W := mkw 0x5e536d029ca4db6d 0xa28021b6de832bde 0xffffffe07fffffff 0xfff387ffff0fffff

def z448 : W := mkw 0x0210000004200040 0x0000000080020140 0x01fe000003fc0003 0x00218001e0078060

def z449 : W := mkw 0xb9e9d04100400080 0x0b8fbeff7fa40220 0xffffffff83e001e3 0x0faffffffff40260

def z450 : W := mkw 0x5401282288005128 0x8680603614c04294 0xfe01fcff8003c1fc 0xfe8c783e1cf0439c

def z451 : W := mkw 0x0000000010808000 0x080f9f4000012800 0x000000e07ffffe00 0x0ccfffc0000ffc00

def z452 : W := mkw 0x2bdad50014a48a45 0x290993c9eb03294a 0x01fe030003fc0603 0x017183c1e3078c63

def z453 : W := mkw 0xf9e9f265814144a2 0x4f8972bf7fe44631 0xffffffff83e3c7e3 0xeffd7a3ffff44e73

def z454 : W := mkw 0xc0a0a265814144a2 0x4e89522901e44631 0x01f003ff83e3c7e3 0xe1f1020103f44e73

def z455 : W := mkw 0x540128aaa8025128 0x8e8ffe7614d85294 0xfe01fcfffc03f9fc 0xfe8ffffe1cf8739c

def z456 : W := mkw 0x0842450000040a05 0x200000804a00000a 0x0001ff0000000000 0xf11000001f00001f

def z457 : W := mkw 0x0842450010848a05 0x200001804a01280a 0x0001ffe07ffffe00 0xfdd387c01f0ffc1f

def z458 : W := mkw 0x0000002c3193a000 0x04405f4000417c00 0x000000e07ffffe00 0x0cc3ffc0000ffc00

def z459 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x3e0ffce07c1ff9fc 0xfe8285c2fc0bf39c

def z460 : W := mkw 0x8a72454114e48ac5 0x2a8901a9caa72b6a 0xffffffffffffffff 0xffff87ffffffffff

def z461 : W := mkw 0x100100fc7393a000 0x0c4fff56147dfc00 0xfe01fcfffffffe00 0x0ecffffe1cfffc00

def z462 : W := mkw 0x4080a20080004422 0x4000201011000011 0x0001e30000000000 0xe110000013000013

def z463 : W := mkw 0x540128fefb93f128 0x86c66d3614fdfe94 0xfe01fcfffffffffc 0xfece7c3e1cffff9c

def z464 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e07ffc0000 0x08838000000f8000

def z465 : W := mkw 0x5401280288005128 0x8280203614800294 0xc000000000000000 0x0000003c00000000

def z466 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xc00000fffc03f800 0x0c8e7c3c00f87000

def z467 : W := mkw 0x000000545391a000 0x084f9f400025ac00 0x0000000003fc0600 0x0c4fffc000078c00

def z468 : W := mkw 0x4400280288005128 0x8280002000800294 0x00000000000001fc 0xf00000000000039c

def z469 : W := mkw 0xc0202201804044a2 0x4280002000800231 0x00000000000001e3 0xe030000000000273

def z470 : W := mkw 0xa73400030c6801d0 0x0aaf802fa08203e0 0xfffe0000000001ff 0x0a2f803fe00003e0

def z471 : W := mkw 0x440028aaa8025128 0x86864c2000d85294 0x000000fffc03f9fc 0xfc8e7c0000f8739c

def z472 : W := mkw 0xc0202265814144a2 0x4e89522000e44631 0x000000ff83e3c7e3 0xecfd7a0000f44e73

def z473 : W := mkw 0xc8e2e76591c5cea7 0x6e8973b95be56e3b 0xc1f1ffff83e3ffe3 0xfffd7ffd1ff47e7f

def z474 : W := mkw 0x000000fc7393a000 0x0c4fc100007dfc00 0x000000fffffffe00 0x08cf800000fffc00

def z475 : W := mkw 0x8020024501410482 0x4000000000240421 0x0000000003e00603 0x0070000000040c63

def z476 : W := mkw 0xca72676595e5cee7 0x668041a0cae76f7b 0x3fffffffffffffff 0xfff387c3ffffffff

def z477 : W := mkw 0x000000ec21030000 0x0c0f5e00007c5400 0x000000ffffe3fe00 0x0ccf7e0000fc7c00

def z478 : W := mkw 0x0210000004200040 0x0000000080020140 0x3ffe0000000001ff 0x02200003e00003e0

def z479 : W := mkw 0xaf7440d34e6801d0 0x0aaf80afeabe83e0 0xfffffffffffc01ff 0x0faf87ffffff83e0

def z480 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc001e31f8003c600 0xe55c7a3c13f04c13

def z481 : W := mkw 0xe7b4a2f7cf6945f2 0x4eaff23fb1fec7f1 0xfffe00fffffc01ff 0x0aaff83fe0ff83e0

def z482 : W := mkw 0x7d4978aaa8025128 0x8786ecf67ed85294 0xfe0ffcfffc03f9fc 0xfe8efdfefcf8739c

def z483 : W := mkw 0x000000a820020000 0x04064c0000585000 0x0000001f80000000 0x000c780000f00000

def z484 : W := mkw 0xa52400d34a480190 0x0aaf802f20bc82a0 0xc00000fffffc0000 0x088f803c00ff8000

def z485 : W := mkw 0x7dc9f8aaa8025128 0x8f8ffeff7fd85294 0xffffff1f80000000 0x0f0ffffffff00000

def z486 : W := mkw 0x8020004100400080 0x0a89002900a40220 0xc000001f80000000 0x000c003c00f00000

def z487 : W := mkw 0x0000000000000000 0x0000000000000000 0x3e01fc00000001fc 0xf20000021c00039c

def z488 : W := mkw 0x0210000014a08040 0x0000010080032940 0x3ffe00e07fffffff 0x0ee387c3e00fffe0

def z489 : W := mkw 0x0840400000000000 0x000000804a000000 0x3e0e1c0000000000 0x000285c2ec000000

def z490 : W := mkw 0x0842450010848a05 0x200001804a01280a 0x3fffff000003fe00 0xff5387c3ff007c1f

def z491 : W := mkw 0x040000fe7b93a100 0x0ecfdf6600fdfe80 0xfe0000fffffffffc 0x0ecffffe00ffff80

def z492 : W := mkw 0x3fddd0924e280150 0x092fbedfff1a81c0 0xffffff007c1c001c 0x0f0fffffff0b8180

def z493 : W := mkw 0x5481a8aaa8025128 0x8e8f7e3f15d85294 0xfff1fffffc03f9fc 0xff8f7e3f1ff8739c

def z494 : W := mkw 0xa73400d34e6801d0 0x02a68026a0be83e0 0x3e0e00fffffc01ff 0x00a28002e0ff83e0

def z495 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x3fffffe07fffffff 0xf3f00003ff0fffff

def z496 : W := mkw 0xa73400f74f6901d0 0x0eafd22fa0fec7e0 0xfffe00ffffffc7ff 0x0eeffa3fe0ffcfe0

def z497 : W := mkw 0x0002050010848a05 0x200001000001280a 0x000000000003fe00 0xf050000000007c1f

def z498 : W := mkw 0x3bdbd50014a48a45 0x290fbfdfff03294a 0xffffff0003fc0603 0x0f7fffffff078c63

def z499 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x3ffe1f007ffc3e1f 0x117387c3ef0fbdef

def z500 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x3e0fff007c1ffe1c 0xf55287c2ff0bfd9f

def z501 : W := mkw 0x0a52455457b5aa45 0x284993c0ca27ad4a 0x3fffffe07fffffff 0xfff387c3ff0fffff

def z502 : W := mkw 0x8020000100400080 0x0280002900800220 0xc1f00000000001e3 0x0220003d00000260

def z503 : W := mkw 0x0e5245821ca48b45 0x228601a6ca9b2bca 0xffffffffffffffff 0xffff87ffffffffff

def z504 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffe001f800001ff 0x022c003fe0f003e0

def z505 : W := mkw 0x29c8d00000000000 0x010000896b000000 0x01fe030000000000 0x01000001e3000000

def z506 : W := mkw 0xf1a9b265814144a2 0x4f8ffe7f35e44631 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z507 : W := mkw 0x271400924e280150 0x00268006a01a81c0 0x3ffe00e07ffc01ff 0x0aa38003e00f83e0

def z508 : W := mkw 0x318990fc63132000 0x0d4ffe5f357cd400 0xc000001f80000000 0x000c783c00f00000

def z509 : W := mkw 0xc63428fbee6a51f8 0x86a0402080fed3f4 0x000000fffffff9ff 0xf0a0000000fff3fc

def z510 : W := mkw 0x5401282aa8025128 0x86806c3614c05294 0xfe01fc000003f9fc 0xf6007c3e1c00739c

def z511 : W := mkw 0x1001000000000000 0x00002c1014000000 0x0001fc0000000000 0x04007c001c000000

def z512 : W := mkw 0x8af2c74515e58ec7 0x68091389cb272d6b 0x3fffffe07fffffff 0xfff387c3ff0fffff

def z513 : W := mkw 0x0840400000000000 0x000000804a000000 0x01fe030000000000 0x010183c1e3000000

def z514 : W := mkw 0x0080800000000000 0x0809321911000000 0xc000000000000000 0x000c783c00000000

def z515 : W := mkw 0xa7b480d34e6801d0 0x0aafb23fb1be83e0 0xffffe3fffffc01ff 0x0faffa3ff3ff83e0

def z516 : W := mkw 0x7dc9f80288005128 0x8b8fbeff7f800294 0xffffff00000001fc 0xff0fffffff00039c

def z517 : W := mkw 0x4a52652094a4ca65 0x268061b0dac36b5a 0xffffffffffffffff 0xffffffffffffffff

def z518 : W := mkw 0x5e536daabca6db6d 0xa6866db6dedb7bde 0xfe0ffcfffc1ff9fc 0xfe8efdfefcfbf39c

def z519 : W := mkw 0x0840400000000000 0x000000804a000000 0x3fffffe003e3c7e3 0xeff387c3ff044e73

def z520 : W := mkw 0x7dc9f8aaa8025128 0x87866cbf7fd85294 0xfffffffffc03f9fc 0xff8e7c3ffff8739c

def z521 : W := mkw 0xbfffd5d35eec8bd5 0x2bafbfffffbfabea 0xffffffffffffffff 0xffffffffffffffff

def z522 : W := mkw 0xc0a0a275d3d1e4a2 0x4ec9f37911e5ee31 0xc1f1e3ff83ffc7e3 0xeffdfbfd13f7ce73

def z523 : W := mkw 0xabfcd051466800d0 0x092992c9eb268160 0x01fe030003fc0003 0x012183c1e3078060

def z524 : W := mkw 0x000000d45391a000 0x084f9340003dac00 0x000000fffffc0600 0x08cf83c000ff8c00

def z525 : W := mkw 0x80a0824501410482 0x4809120901240421 0x0000000000000000 0x0000000000000000

def z526 : W := mkw 0x0400008208000100 0x0286002600980280 0xc000001f80000000 0x000c003c00f00000

def z527 : W := mkw 0xf9e9f265814144a2 0x4f8ffeff7fe44631 0xffffff1f80000000 0x0f0ffffffff00000

def z528 : W := mkw 0x0000006401010000 0x0c09520000644400 0x0000001f80000000 0x000c780000f00000

def z529 : W := mkw 0xa52400d34a480190 0x0aaf802f20bc82a0 0xfe0000fffc0001fc 0x0a8e003e00f80380

def z530 : W := mkw 0x50012828a0025028 0x84006c1014405014 0x0000000000000000 0x0000780000000000

def z531 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x3fffff0003fc0603 0x0f7387c3ff078c63

def z532 : W := mkw 0x0400088a28021108 0x8000000000181084 0x000000007c00381c 0x100000000008318c

def z533 : W := mkw 0x540128aab882d128 0x86866d3614d97a94 0xfe01fcfffffffffc 0xfecffffe1cffff9c

def z534 : W := mkw 0x021000d046200040 0x080f8000803e8140 0x3ffe00fffffc01ff 0x0aaf8003e0ff83e0

def z535 : W := mkw 0x863400d34e6801d0 0x0aaf802080be83e0 0x000000fffffc01ff 0x08af800000ff83e0

def z536 : W := mkw 0x18c9d00000000000 0x090fbed05f000000 0x0001ff0000000000 0x0d0fffc01f000000

def z537 : W := mkw 0x3dc9d08208000100 0x0b8fbeff7f980280 0xfffffffffc0001fc 0x0f8ffffffff80380

def z538 : W := mkw 0x0000007c7393a000 0x0c49df400065fc00 0x0000000003fffe00 0x0441ffc00007fc00

def z539 : W := mkw 0xf52528fbea4a51b8 0x8eafec3f34fcd2b4 0xc000001f80000000 0x000c783c00f00000

def z540 : W := mkw 0xc0a0a225814144a2 0x4680723911c04631 0xc1f1e3000003c7e3 0xe7707a3d13004e73

def z541 : W := mkw 0x0212050014a48a45 0x200001008003294a 0x0000000003fc0603 0x0070000000078c63

def z542 : W := mkw 0x0000000000000000 0x0000000000000000 0x3e0000e07c0001fc 0x0a82000200080380

def z543 : W := mkw 0x440020a288004120 0x0686603610d84290 0xfe01e0fffc03c1fc 0xee8e783e10f84390

def z544 : W := mkw 0xd4a1aafffbd3f5aa 0xcecfff7f15fdfeb5 0xfff1ffffffffffff 0xffffffff1fffffff

def z545 : W := mkw 0x0080800000000000 0x0809321911000000 0xc1f1e3e003e3c7e3 0xeffd7a3d13044e73

def z546 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x3e0e1ce07fffffff 0xf0f285c2ec0fffff

def z547 : W := mkw 0xc4a0a2e7894145a2 0x4e8f723f11fc46b1 0xfff1e3ffffe3c7ff 0xefff7a3f13fc4ff3

def z548 : W := mkw 0xc0a0a2fde35364a2 0x4ecffe7911fcd631 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z549 : W := mkw 0x3bdbd50004240a45 0x2100209fff02014a 0xffffff00000001ff 0xf330003fff0003ff

def z550 : W := mkw 0x80a0825553d1a482 0x484993490125ac21 0x01f0030003fc0603 0x017183c103078c63

def z551 : W := mkw 0xf73528fbee6a51f8 0x8eafec3fb4fed3f4 0xfffe00fffffc01ff 0x0aaff83fe0ff83e0

def z552 : W := mkw 0x0000005042000000 0x0809800000248000 0x0000000003fc0000 0x0001800000078000

def z553 : W := mkw 0x2bdad50014a48a45 0x290993c9eb03294a 0x3fffffe07fffffff 0xfff387c3ff0fffff

def z554 : W := mkw 0x0000000010808000 0x0000010000012800 0x000000000003fe00 0x044007c000007c00

def z555 : W := mkw 0xe9e8f265814144a2 0x4f89f2f97be44631 0xc1ffe3ff83e3c7e3 0xeffdfbfdf3f44e73

def z556 : W := mkw 0xa3340001046800d0 0x00200009a0020160 0x01fe000000000003 0x00200001e0000060

def z557 : W := mkw 0x0a52450004240a45 0x20000080ca02014a 0x3fffffe07c03f9ff 0xffb20403ff0873ff

def z558 : W := mkw 0x540128fefb93f128 0x8ecfff7614fdfe94 0xc00000fffffffe00 0x0ccffffc00fffc00

def z559 : W := mkw 0x0400008208000100 0x0280002000980280 0x000000fffc0001fc 0x0080000000f80380

def z560 : W := mkw 0x0080820401010402 0x4000120001000401 0x0000030000000600 0x0150020003000c03

def z561 : W := mkw 0xaf7645ff7fffabd5 0x2eefdfefeaffffea 0xffffffffffffffff 0xffffffffffffffff

def z562 : W := mkw 0x0a52450004240a45 0x20000080ca02014a 0x3e0e1c000000001c 0x10000002ec00018c

def z563 : W := mkw 0x3189900000000000 0x090fbe5f35000000 0xfe01fc0000000000 0x0e0e7c3e1c000000

def z564 : W := mkw 0x540128aaa8025128 0x84066c1614585094 0x3e01fc007c03f81c 0xf4027c021c08719c

def z565 : W := mkw 0x000000fc63132000 0x0c4fde40007cd400 0x000000ff83e3c600 0x0ccd7a0000f44c00

def z566 : W := mkw 0x000000a820020000 0x0c0fde4000585000 0x000000fffc03f800 0x0c8fffc000f87000

def z567 : W := mkw 0x0a52455457b5aa45 0x284993c0ca27ad4a 0x01fe030003fc0603 0x017183c1e3078c63

def z568 : W := mkw 0x540128aaa8025128 0x8680603614d85294 0xfe01fcfffc03f9fc 0xf280003e1cf8739c

def z569 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x3e0e1ce07ffffe1c 0x1cc387c2ec0ffd8c

def z570 : W := mkw 0x0000006401010000 0x0c09520000644400 0x01f1e3ff83e3c7e3 0xeffd7a0113f44e73

def z571 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffff0000000000 0x030c783fff000000

def z572 : W := mkw 0x0a52450014a48a45 0x20000180ca03294a 0x01fe03e07fffffff 0xf1f183c1e30fffff

def z573 : W := mkw 0xf73528038c6851f8 0x82a0203fb48203f4 0xfffffc00000001ff 0xf220003ffc0003fc

def z574 : W := mkw 0xfde9faefa94355aa 0xcf8ffeff7ffc56b5 0xffffffffffe3ffff 0xfffffffffffc7fff

def z575 : W := mkw 0xab76455156ec8ad5 0x28298189ea27a96a 0x3fffffe07fffffff 0xfff387c3ff0fffff

def z576 : W := mkw 0xc0a0a265814144a2 0x4680603911e44631 0xc1f1e3ff83e3c7e3 0xe3f0003d13f44e73

def z577 : W := mkw 0x0a52456415a58a45 0x2c095380ca676d4a 0x3fffffffffffffff 0xffffffc3ffffffff

def z578 : W := mkw 0x0000000000000000 0x0006000600000000 0xfe00000000000000 0x0a0e003e00000000

def z579 : W := mkw 0x82340051466800d0 0x0020000080268160 0x0000000003fc0003 0x0020000000078060

def z580 : W := mkw 0x3bdbd50004240a45 0x290fbedfff02014a 0xffffff00000001ff 0xff3fffffff0003ff

def z581 : W := mkw 0xa73400fb6e6a01d0 0x0eafcc2fa0fed3e0 0xfffe00fffffff9ff 0x0eaffc3fe0fff3e0

def z582 : W := mkw 0x18cbd50010848a05 0x21003fd05f01280a 0x0001ff000003fe00 0xf5507fc01f007c1f

def z583 : W := mkw 0x39cbd50010848a05 0x290fbfdf7f01280a 0xffffff000003fe00 0xff5fffffff007c1f

def z584 : W := mkw 0x0842452c3197aa05 0x24405fc04a417c0a 0x0001ff000003fe00 0xf5507fc01f007c1f

def z585 : W := mkw 0x3189900000000000 0x090fbe5f35000000 0xc000000000000000 0x0c0ffffc00000000

def z586 : W := mkw 0x0000000010808000 0x0000010000012800 0x0000000003fc0600 0x004183c000078c00

def z587 : W := mkw 0xaf7645031cec8bd5 0x22a001afea832bea 0xffffffe07fffffff 0xfff387ffff0fffff

def z588 : W := mkw 0xd8e9f265814144a2 0x4f897ef95fe44631 0xc1f1ffff83e3c7e3 0xeffd7ffd1ff44e73

def z589 : W := mkw 0x0a52450004240a45 0x20000080ca02014a 0x3fffffe003e3c7ff 0xfff10203ff044fff

def z590 : W := mkw 0x5481aaaea903552a 0xc6867e3615d85695 0xfe01fffffc03fffc 0xffde7e3e1ff87f9f

def z591 : W := mkw 0x000000987292a000 0x004001000019b800 0x000000007c1c3800 0x00000000000bb000

def z592 : W := mkw 0x440028aaa8025128 0x8680402000d85294 0x0000001f80000000 0x0000000000f00000

def z593 : W := mkw 0x0000004401010000 0x0809120000240400 0x0000000003e00600 0x0041020000040c00

def z594 : W := mkw 0x863400d34e6801d0 0x02a6002680be83e0 0xfe0000fffffc01ff 0x0aae003e00ff83e0

def z595 : W := mkw 0x000000d042000000 0x00000000003c8000 0x000000fffffc0000 0x0080000000ff8000

def z596 : W := mkw 0x0000000000000000 0x0000000000000000 0x000000e003e3c7e3 0xe0f0000000044e73

def z597 : W := mkw 0x3b5b550014a48a45 0x21068dc6ee03294a 0x3e0e1c007c1c381c 0x100285c2ec0bb18c

def z598 : W := mkw 0xc4a0aaefa94355aa 0xce89723911fc56b5 0xc1f1e3ffffe3ffff 0xfffd7a3d13fc7fff

def z599 : W := mkw 0x0000000000000000 0x0000000000000000 0x0000000000000000 0x0000000000000000

def z600 : W := mkw 0xa73400534e6801d0 0x0aa9802fa0a683e0 0xfffe000003fc01ff 0x0221803fe00783e0

def z601 : W := mkw 0x400020a8a0024020 0x06866c3010d85210 0xc001e0fffc03f9e0 0xee8e7c3c10f87210

def z602 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xc00000fffffc01ff 0x00ac003c00ff83e0

def z603 : W := mkw 0x5401280288005128 0x82862c3614800294 0xfe01fc00000001fc 0xfe0e7c3e1c00039c

def z604 : W := mkw 0x7fdbfdaabca6db6d 0xaf8fffffffdb7bde 0xffffffffffffffff 0xffffffffffffffff

def z605 : W := mkw 0x0842450010848a05 0x200001804a01280a 0x0000030000000600 0x015003c003000c03

def z606 : W := mkw 0x0400008208000100 0x0006000600180080 0x3e0000007c00001c 0x0002000200080180

def z607 : W := mkw 0x18c9d00000000000 0x010020905f000000 0x0001ff0000000000 0x010000001f000000

def z608 : W := mkw 0x140108aa28021108 0x84064c0604585084 0x3e001cfffc03f81c 0x1c8e7c020cf8718c

def z609 : W := mkw 0xa73605d35eec8bd5 0x2aaf812fa0bfabea 0xfffe00ffffffffff 0xfaff803fe0ffffff

def z610 : W := mkw 0x0210000004200040 0x0000000080020140 0x3e0e00007c1c001c 0x00028002e00b8180

def z611 : W := mkw 0x4080a22481014422 0x4400721011404411 0x01f1e3e003e3c7e3 0xeff17a0113044e73

def z612 : W := mkw 0x0000000000000000 0x0809120000000000 0x0000000000000000 0x0c0d7a0000000000

def z613 : W := mkw 0x000000987292a000 0x00468d400019b800 0x000000e07ffffe00 0x0cc387c0000ffc00

def z614 : W := mkw 0xd0a1a265814144a2 0x4e8f7e3f15e44631 0xfff1ffff83e3c7e3 0xefff7e3f1ff44e73

def z615 : W := mkw 0x5a536d28b4a6da6d 0xa4006d90de43795e 0x3fffffe07fffffff 0xfff3ffc3ff0fffff

def z616 : W := mkw 0x39c9d00000000000 0x0100209f7f000000 0xffffff0000000000 0x0f0387ffff000000

def z617 : W := mkw 0x39c9d0a820020000 0x0d0ffedf7f585000 0xfffffffffc03f800 0x0f8ffffffff87000

def z618 : W := mkw 0xf1a9b265814144a2 0x4f8ffe7f35e44631 0xc000001f80000000 0x000c783c00f00000

def z619 : W := mkw 0x1e534d8a3ca69b4d 0xa0060d86ce1b39ce 0x3fffffe07fffffff 0xfff387c3ff0fffff

def z620 : W := mkw 0x0a52450004240a45 0x20000080ca02014a 0x3fffffe07ffc01ff 0xfbb38003ff0f83ff

def z621 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc001e0ff8003c1e0 0xee8c783c10f04210

def z622 : W := mkw 0x000000bc7393a000 0x0446df400059fc00 0x000000007c1ffe00 0x0442ffc0000bfc00

def z623 : W := mkw 0xc0a0a2f5c34144a2 0x4e8ff23911fcc631 0xc1f1e3ffffffc7e3 0xeffffa3d13ffce73

def z624 : W := mkw 0xf73528abac6a51f8 0x86a66c3fb4da53f4 0xfffffcfffc03f9ff 0xfeae7c3ffcf873fc

def z625 : W := mkw 0x58c9f22481014422 0x45007ed05f404411 0x0001ff000003c600 0xe5507fc01f004c13

def z626 : W := mkw 0x0000000000000000 0x0809000900000000 0xc1f0000000000000 0x0a0d003d00000000

def z627 : W := mkw 0x1401088a28021108 0x82860c2604981284 0xfe001cfffc0039fc 0x1a8e043e0cf8338c

def z628 : W := mkw 0x0000000000000000 0x080f9e4000000000 0x0000000000000000 0x000c780000000000

def z629 : W := mkw 0x0000009042000000 0x0006800000188000 0x000000007c1c0000 0x00028000000b8000

def z630 : W := mkw 0x1401088a28021108 0x80060c0604181084 0x0000000000000000 0x0000000000000000

def z631 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xc001fc1f8003f800 0xf40c7c3c1cf0701c

def z632 : W := mkw 0xbdedd0d34a480190 0x0bafbeff7fbc82a0 0xffffff1f80000000 0x0f0ffffffff00000

def z633 : W := mkw 0x7589b8aaa8025128 0x8f8ffe7f35d85294 0xc000001f80000000 0x000c783c00f00000

def z634 : W := mkw 0x394950fc7393a000 0x0d4fdfc66e7dfc00 0x3e0e1cfffffffe00 0x0ccfffc2ecfffc00

def z635 : W := mkw 0x061000820c200140 0x02860026809a03c0 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z636 : W := mkw 0x084245fc7397aa05 0x2c4fdfc04a7dfc0a 0x0001fffffffffe00 0xfddfffc01ffffc1f

def z637 : W := mkw 0x000000fc7393a000 0x04464d00007dfc00 0x000000fffffffe00 0x0cce7c0000fffc00

def z638 : W := mkw 0x0ad2c50014a48a45 0x28093399db03294a 0xffffffe07fffffff 0xffffffffff0fffff

def z639 : W := mkw 0x394950987292a000 0x01468dc66e19b800 0x3e0e1c007c1c3800 0x000285c2ec0bb000

def z640 : W := mkw 0x39c9d00000000000 0x090fa09f7f000000 0xffffff0000000000 0x0b0f803fff000000

def z641 : W := mkw 0x863400d34e6801d0 0x02a0002080be83e0 0x3ffe00fffffc01ff 0x0aa38003e0ff83e0

def z642 : W := mkw 0xab76455156ec8ad5 0x28298189ea27a96a 0x01fe030003fc0603 0x017183c1e3078c63

def z643 : W := mkw 0xe5a4a2f7cb4945b2 0x4eaff23f31fcc6b1 0xc000001f80000000 0x000c783c00f00000

def z644 : W := mkw 0x5e536dfeffb7fb6d 0xaecffff6deffffde 0xffffffffffffffff 0xffffffffffffffff

def z645 : W := mkw 0x0000002c21132000 0x04405e4000405400 0x0000000000000000 0x0000780000000000

def z646 : W := mkw 0x540128eea9035128 0x8e8f7e3614fc5694 0xfe01fcffffe3fffc 0xfecf7e3e1cfc7f9c

def z647 : W := mkw 0x0000000000000000 0x0000000000000000 0x01f1e30000000000 0x0f01020113000000

def z648 : W := mkw 0x0000000000000000 0x0000000000000000 0x3e001c007c00381c 0x100204020c08318c

def z649 : W := mkw 0x0210000004200040 0x0000000080020140 0x3fffe3e07fffc7ff 0xeff38203f30fcff3

def z650 : W := mkw 0x271400020c280150 0x00200006a00201c0 0x3e0e00000000001c 0x00000002e0000180

def z651 : W := mkw 0xa73400d34e6801d0 0x0aa98029a0be83e0 0x01fe00fffffc01ff 0x00a18001e0ff83e0

def z652 : W := mkw 0x79c9f22481014422 0x4d0ffedf7f404411 0xffffff000003c600 0xef5fffffff004c13

def z653 : W := mkw 0x29c8d0fc7393a000 0x0d4fdfc96b7dfc00 0x01fe03fffffffe00 0x0dcfffc1e3fffc00

def z654 : W := mkw 0x4000202080004020 0x0680402000c04210 0x000000ff8003c1e0 0xe080000000f04210

def z655 : W := mkw 0xc0a0a2fde35364a2 0x4ecffe7911fcd631 0xc000001f80000000 0x000c783c00f00000

def z656 : W := mkw 0xc0202265814144a2 0x4680402000e44631 0x0000001f80000000 0x0000000000f00000

def z657 : W := mkw 0x0212050014a48a45 0x200001008003294a 0x3ffe00e07fffffff 0xfaf38003e00fffff

def z658 : W := mkw 0x3189900000000000 0x0100201f35000000 0xc000000000000000 0x0000003c00000000

def z659 : W := mkw 0xf9e9f2fdf3d3e4a2 0x4fcfffff7ffdfe31 0xffffffffffffffe3 0xeffffffffffffe73

def z660 : W := mkw 0x0a5245d056a48a45 0x280f8180ca3fa94a 0x3fffffffffffffff 0xffff87c3ffffffff

def z661 : W := mkw 0xbffdd0030c6801d0 0x0bafbeffff8203e0 0xffffff00000001ff 0x0f2fffffff0003e0

def z662 : W := mkw 0x440028aaa8025128 0x8686402600d85294 0xfe0000fffc03f9fc 0xfa8e003e00f8739c

def z663 : W := mkw 0xc0a0a201804044a2 0x4280203911800231 0xc1f1e3e003e3c7e3 0xeff1023d13044e73

def z664 : W := mkw 0x39c9d00000000000 0x01062c9f7f000000 0xffffff0000000000 0x0f0e7c3fff000000

def z665 : W := mkw 0x5401288288005128 0x8286203614980294 0xfe01fcfffc0001fc 0xfa8e003e1cf8039c

def z666 : W := mkw 0xc8e0e265814144a2 0x4e8972b95be44631 0xffffffff83e3c7e3 0xeffffffffff44e73

def z667 : W := mkw 0x540128aeb993f128 0x86c67f7614d97e94 0xfe01fcfffc03fffc 0xfece7ffe1cf87f9c

def z668 : W := mkw 0x80a0804100400080 0x0a89323911a40220 0xc1f1e3ff83e001e3 0x0fad7a3d13f40260

def z669 : W := mkw 0xe73428fbee6a51f8 0x8eafc02fa0fed3f4 0xfffe00fffffff9ff 0xfaaf803fe0fff3fc

def z670 : W := mkw 0xd0a1aa6da14354aa 0xce897e3915e45635 0xc1f1ffff83e3ffe3 0xfffd7e3d1ff47e7f

def z671 : W := mkw 0xbbfdd051466800d0 0x092fbedfff268160 0xffffff0003fc0003 0x0f2fffffff078060

def z672 : W := mkw 0xcaf2e76585654ee7 0x6e8972b9dbe6477b 0xffffffff83e3c7ff 0xfffd7a3ffff44fff

def z673 : W := mkw 0xf73528d3ce6851f8 0x8aafa03fb4be83f4 0xfffffcfffffc01ff 0xfaaf803ffcff83fc

def z674 : W := mkw 0x000000d052808000 0x080f8100003da800 0x000000fffffffe00 0x0ccf87c000fffc00

def z675 : W := mkw 0x0000000000000000 0x0000000000000000 0x3ff1ffe07fe3ffff 0xfff306031f0c7fff

def z676 : W := mkw 0xa73400030c6801d0 0x02a0002fa08203e0 0xfffe00e07ffc01ff 0x0aa3803fe00f83e0

def z677 : W := mkw 0x0000000000000000 0x0809924000000000 0x0000000000000000 0x000183c000000000

def z678 : W := mkw 0xf9e9f201804044a2 0x4b8fbeff7f800231 0xffffff00000001e3 0xef3fffffff000273

def z679 : W := mkw 0xa124005142480090 0x0829800920248020 0x0000000000000000 0x0000000000000000

def z680 : W := mkw 0xd42128eba84251a8 0x8e8f6c3f14fc52b4 0xfff1fcffffe3f9ff 0xfeaf7c3f1cfc73fc

def z681 : W := mkw 0xe7b4a2038c6845f2 0x42a0203fb18203f1 0xffffe300000001ff 0xe330003ff30003f3

def z682 : W := mkw 0x2100000000000000 0x0000000f20000000 0xfffe000000000000 0x0200003fe0000000

def z683 : W := mkw 0x021205fc77b7aa45 0x2c4fdf40807ffd4a 0x000000ffffffffff 0xfcffffc000ffffff

def z684 : W := mkw 0x0000000000000000 0x0000000000000000 0x0001e3000003c600 0xe550020013004c13

def z685 : W := mkw 0x3bdbd50014a48a45 0x290fbfdfff03294a 0xffffff007c1c381c 0x1f0fffffff0bb18c

def z686 : W := mkw 0xd4a1aa03884055aa 0xc280203f158002b5 0xfff1ff00000001ff 0xf330003f1f0003ff

def z687 : W := mkw 0x0000006c3193a000 0x0c495f4000657c00 0x000000ff83e3fe00 0x0ccd7fc000f47c00

def z688 : W := mkw 0x39c9d00000000000 0x0909b2df7f000000 0xffffff0000000000 0x030183ffff000000

def z689 : W := mkw 0x1401080208001108 0x8000000604000084 0x3e001c000000001c 0x100000020c00018c

def z690 : W := mkw 0x000000fc7393a000 0x04404100007dfc00 0x000000fffffffe00 0x0cc387c000fffc00

def z691 : W := mkw 0x50012828a0025028 0x84066c1614405014 0xfe01fc000003f800 0xfe0e7c3e1c00701c

def z692 : W := mkw 0xc0a0a2fdf3d3e4a2 0x4ec9733911fdfe31 0xc1f1e3ffffffffe3 0xeffd7a3d13fffe73

def z693 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc00000ff83e3c7e3 0xe0fc783c00f44e73

def z694 : W := mkw 0xc0a0a2fdf3d3e4a2 0x4ecfff7911fdfe31 0xc00000fffffffe00 0x0ccffffc00fffc00

def z695 : W := mkw 0x1001080820021008 0x80000c0004001004 0x00001c0000003800 0x100004000c00300c

def z696 : W := mkw 0x0000004000000000 0x0809000000240000 0x000000ff83e00000 0x088d000000f40000

def z697 : W := mkw 0x271400d24e280150 0x082f8006a03e81c0 0x3e0e00fffffc001c 0x088f8002e0ff8180

def z698 : W := mkw 0xd4a1aaefa94355aa 0xce8f7e3f15fc56b5 0xc000001f80000000 0x000c783c00f00000

def z699 : W := mkw 0xb7bd90d34e6801d0 0x0bafbe7fb5be83e0 0xfffe00fffffc01ff 0x0aaff83fe0ff83e0

def z700 : W := mkw 0xeff6e7f7dfedcff7 0x6eaff3bffbffeffb 0xffffffffffffffff 0xffffffffffffffff

def z701 : W := mkw 0xc63422f7cf6945f2 0x46a0402080fec7f1 0x000000ffffffc7ff 0xe0f0000000ffcff3

def z702 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f1e31f800001e3 0xe33c783d13f00273

def z703 : W := mkw 0x000000fc63132000 0x04404000007cd400 0x0000001f80000000 0x0000000000f00000

def z704 : W := mkw 0x000000fc7393a000 0x0446cd40007dfc00 0x000000fffffffe00 0x00c285c000fffc00

def z705 : W := mkw 0xa3b48255476904d2 0x48299209a1268561 0x01fe030003fc0603 0x01718201e3078c63

def z706 : W := mkw 0x500128fcf393f028 0x8c4fff50147dfc14 0x0001fcfffffffe00 0xfccfffc01cfffc1c

def z707 : W := mkw 0x4000206481014020 0x0e89723010e44610 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z708 : W := mkw 0x6794a2b6cf294572 0x4426f216b15ac5d1 0x3e0fe3007c1fc61c 0xe552fa02f30bcd93

def z709 : W := mkw 0x3949500000000000 0x090fbed67e000000 0xfe0ffc0000000000 0x0e0ffffefc000000

def z710 : W := mkw 0x6dc8f8aaa8025128 0x8f89d2e96bd85294 0x01fe03fffc03f9fc 0xf18183c1e3f8739c

def z711 : W := mkw 0xfffdf2038c6845f2 0x43a020bfff8203f1 0xffffff00000001ff 0xe330003fff0003f3

def z712 : W := mkw 0x0840400000000000 0x000020905a000000 0xffffff0000000000 0x0f0fffffff000000

def z713 : W := mkw 0x39c9d20401010402 0x490fbedf7f000401 0xffffff0000000600 0x0f5fffffff000c03

def z714 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x000000fffffffe00 0x00cdfbc000fffc00

def z715 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xc001fcfffc03f9fc 0xf48c7c3c1cf8739c

def z716 : W := mkw 0x863400d34e6801d0 0x0aa9002980be83e0 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z717 : W := mkw 0x000000745391a000 0x0c49d3400065ec00 0x0000001f83fc0600 0x004dfbc000f78c00

def z718 : W := mkw 0x7d4978aaa8025128 0x8786cce66ed85294 0x3e0e1cfffc03f9fc 0xf08285c2ecf8739c

def z719 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xfff1ffff83e3c7e3 0xefff7e3f1ff44e73

def z720 : W := mkw 0xb73500d34e6801d0 0x0aaf8c2fa4be83e0 0xfffe1cfffffc01ff 0x0aaf843fecff83e0

def z721 : W := mkw 0x100100fc7393a000 0x0c4fdf46047dfc00 0x3e001cfffffffe00 0x0ccfffc20cfffc00

def z722 : W := mkw 0x08c0c00000000000 0x080fbed95b000000 0xffffff0000000000 0x0f0fffffff000000

def z723 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffe001ffffc001f 0x002f803fe0ff81e0

def z724 : W := mkw 0x39c9d00000000000 0x0106bed67f000000 0xfe0fff0000000000 0x0f0efffeff000000

def z725 : W := mkw 0x4a52652094a4ca65 0x268061b0dac36b5a 0xfe0ffcfffc1ff9fc 0xfe8efdfefcfbf39c

def z726 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f1e3ffffe3ffe3 0xefff7e3d13fc7e73

def z727 : W := mkw 0xa73400d34e6801d0 0x02a6802fa0be83e0 0xfffe00fffffc01ff 0x02a2803fe0ff83e0

def z728 : W := mkw 0xc0a0a299f2d2e4a2 0x42c6ad791199ba31 0xc1f1e3007c1c39e3 0xe33285fd130bb273

def z729 : W := mkw 0x8862454110c48a85 0x2a8901a94aa52a2a 0xc1f1ffff83e3ffe3 0xfffd07fd1ff47e7f

def z730 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe01fcffffe3fffc 0xfecf7e3e1cfc7f9c

def z731 : W := mkw 0x5e536d028c245b6d 0xa28020b6de8203de 0xfe0ffc00000001fc 0xf200003efc00039c

def z732 : W := mkw 0x39c9d0d042000000 0x090fa09f7f3c8000 0xfffffffffffc0000 0x0b8f803fffff8000

def z733 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xfffe030000000000 0x0b0ffbffe3000000

def z734 : W := mkw 0x29c8d00000000000 0x090fbed97b000000 0xc1ffe30000000000 0x0f0ffffdf3000000

def z735 : W := mkw 0x9efdd0d34e6801d0 0x03a03ef0dfbe83e0 0x0001fffffffc01ff 0x05a07fc01fff83e0

def z736 : W := mkw 0x339b950014a48a45 0x290fbf5fb503294a 0xc00000e07fffffff 0xf0fc783c000fffff

def z737 : W := mkw 0x80a082fd73d3a482 0x4c4fdf49017dfc21 0x000000fffffffe00 0x0ccfffc000fffc00

def z738 : W := mkw 0xb73508db6e6a11d8 0x8aaf8c2fa4be93e4 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z739 : W := mkw 0x271400924e280150 0x0aaf802fa09a83c0 0xfffe00fffc1c01fc 0x0a8f803fe0fb8380

def z740 : W := mkw 0x000000ac3193a000 0x04465f4000597c00 0x000000fffffffe00 0x0ccfffc000fffc00

def z741 : W := mkw 0xdef3ef038c645fef 0xe28020bfdf8203ff 0xffffff00000001ff 0xf330003fff0003ff

def z742 : W := mkw 0x771528baee2a5178 0x8426ec16b45ad1d4 0x3e0ffc007c1ff81c 0xf402fc02fc0bf19c

def z743 : W := mkw 0xc0a0a265814144a2 0x4e89f27911e44631 0xc1f1e3ff83e3c7e3 0xeffdfbfd13f44e73

def z744 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x0000001f83fffe00 0x044dffc000f7fc00

def z745 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x3ffe00fffffffe00 0x0ecfffc3e0fffc00

def z746 : W := mkw 0xe73428d3ce6851f8 0x8aaf802fa0be83f4 0xfffe00fffffc01ff 0xfaaf803fe0ff83fc

def z747 : W := mkw 0x000000b87292a000 0x0c4fdf400059f800 0x000000fffc1ff800 0x0c8fffc000fbf000

def z748 : W := mkw 0x400020a8a0024020 0x06866c3010d85210 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z749 : W := mkw 0xc0a0a221804044a2 0x4680603911c04231 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z750 : W := mkw 0xa73400db6e7a21d0 0x0aef8c6fa0be93e0 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z751 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xffffe0ffffffc1ff 0xeeaf803ff0ffc3f0

def z752 : W := mkw 0x4a52652094a4ca65 0x268061b0dac36b5a 0xc1ffe3ff83ffc7e3 0xeffdfbfdf3f7ce73

def z753 : W := mkw 0xa7b482d34e6805d2 0x4aaf802fa1be83e1 0xfffe03fffffc01ff 0x0bbf803fe3ff83e3

def z754 : W := mkw 0x210000fc7393a000 0x0c4fdf4f207dfc00 0xc00000fffffffe00 0x0ccffffc00fffc00

def z755 : W := mkw 0x040008fe7b93b108 0x8c4fdf40007dfc84 0x000000fffffffe1c 0x1ccfffc000fffd8c

def z756 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe01fc1f8003f9fc 0xf60c7c3e1cf0739c

def z757 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffe001ffc1c01ff 0x022e803fe0fb83e0

def z758 : W := mkw 0xbfffd5030c6c0bd5 0x23a020bfff8203ea 0xffffff00000001ff 0xf330003fff0003ff

def z759 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffe001f83fc0003 0x0a2f803fe0f78060

def z760 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f003ff83e3c7e3 0xe1fd7a3d03f44e73

def z761 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x0000001ffc1ffe00 0x044effc000fbfc00

def z762 : W := mkw 0x000000fc7393a000 0x04464d00007dfc00 0x000000fffffffe00 0x0ccfffc000fffc00

def z763 : W := mkw 0x0a5245fc67372a45 0x2c4fdec0ca7ed54a 0x3fffff1f800001ff 0xf33c7803fff003ff

def z764 : W := mkw 0xad6645d35acc8b95 0x2aaf81af6abdaaaa 0xc001ff1f8003fe00 0xf55c07fc1ff07c1f

def z765 : W := mkw 0x4080a02080004020 0x0e89723911c04210 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z766 : W := mkw 0x80a0804100400080 0x0a89323911a40220 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z767 : W := mkw 0x140108aa28021108 0x84066c1614585084 0xfe01fcfffc03f81c 0x1e8e7c3e1cf8718c

def z768 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfff1fcffffe3f9ff 0xfeaf7c3f1cfc73fc

def z769 : W := mkw 0x000000fc7393a000 0x0c49df40007dfc00 0x000000fffffffe00 0x04c1ffc000fffc00

def z770 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xc1fe030000000000 0x0d0ffffde3000000

def z771 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffff000003c600 0xef5fffffff004c13

def z772 : W := mkw 0xe3b4a275c76944f2 0x4c29f219b166c571 0x01ffe30003ffc603 0xe571fa01f307cc73

def z773 : W := mkw 0x4a52650084244a65 0x228020b0da82035a 0xffffff00000001ff 0xf330003fff0003ff

def z774 : W := mkw 0x3f5f55925eac8b55 0x21268dc6ee1ba9ca 0x3e0e1c007c1c381c 0x100285c2ec0bb18c

def z775 : W := mkw 0x100100a820020000 0x04066c1614585000 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z776 : W := mkw 0x39c9d00000000000 0x01062c9f7f000000 0xffffff0000000000 0x0f0fffffff000000

def z777 : W := mkw 0x94a18acf2943158a 0xc80f1e0f053c14a5 0x3ff01f007fe03e1f 0x117306030f0c3def

def z778 : W := mkw 0xc8606265814144a2 0x468040a04ae44631 0x3fffffff83e3c7e3 0xeff387c3fff44e73

def z779 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x3ff1ffffffffffff 0xffffffc31fffffff

def z780 : W := mkw 0x3b5b559876b6aa45 0x21468dc6ee1bb94a 0x3e0e1c007c1c381c 0x100285c2ec0bb18c

def z781 : W := mkw 0x000000f443010000 0x0c0fde40007cc400 0x000000ffffffc600 0x0ccfffc000ffcc00

def z782 : W := mkw 0xa73400d34e6801d0 0x0aaf8c6fa0be83e0 0xfffe00fffffc01ff 0x0aaf85ffe0ff83e0

def z783 : W := mkw 0xa7b482d74f6905d2 0x4aaf922fa1be87e1 0xffffe3ffffffc7ff 0xefff823ff3ffcff3

def z784 : W := mkw 0xc0a0a255d3d1e4a2 0x4ac9b37911a5ae31 0xc1f1e30003fc07e3 0xe37183fd13078e73

def z785 : W := mkw 0xa734002f3dfba1d0 0x06e05f6fa0c37fe0 0xfffe00000003ffff 0x06607fffe0007fe0

def z786 : W := mkw 0x0000007c7393a000 0x0c49df400065fc00 0x000000ff83fffe00 0x0ccdffc000f7fc00

def z787 : W := mkw 0x540128aaa8025128 0x86806c3014d85294 0xc001fcfffc03f9fc 0xfe8c7c3c1cf8739c

def z788 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe01fcfffc03f9fc 0xf28c783e1cf8739c

def z789 : W := mkw 0xa7bc90d34e6801d0 0x0baf926fa1be83e0 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z790 : W := mkw 0x000000fc7393a000 0x0c4fdf49007dfc00 0xc1f000fffffffe00 0x0ecffffd00fffc00

def z791 : W := mkw 0x008082fc7393a402 0x4c4fdf40017dfc01 0x000003fffffffe00 0x0ddfffc003fffc03

def z792 : W := mkw 0x2f56459a7ebeab55 0x20668dc6ea1bb9ca 0x3e0e1c007c1c381c 0x100285c2ec0bb18c

def z793 : W := mkw 0x863400d34e6801d0 0x0aaf9e6080be83e0 0x000000fffffc01ff 0x0cafffc000ff83e0

def z794 : W := mkw 0x000000a830828000 0x04064d0000597800 0x000000fffc1ff800 0x0c8efdc000fbf000

def z795 : W := mkw 0xa73400d74f7921d0 0x0aef926fa0be87e0 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z796 : W := mkw 0x3949500000000000 0x090f9ecf6e000000 0xfffe1c0000000000 0x0e0fffffec000000

def z797 : W := mkw 0x80a0824501410482 0x4a89323911a40621 0xc1f1e3ff83e007e3 0x0ffd7a3d13f40e63

def z798 : W := mkw 0xa73605d34e6c0bd5 0x2aaf802fa0be83ea 0xfffe00fffffc01ff 0xfabf803fe0ff83ff

def z799 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f1e3ffffe3ffff 0xfffd7a3d13fc7fff

def z800 : W := mkw 0x863400d34e6801d0 0x02a6002680be83e0 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z801 : W := mkw 0xc0202265814144a2 0x4680603010e44631 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z802 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x3e0000fffffffffc 0x0ecfffc200ffff80

def z803 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffff0003e00603 0x0f7fffffff040c63

def z804 : W := mkw 0x5401282288005128 0x8680603614c04294 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z805 : W := mkw 0xa73400d34e6801d0 0x0aa9802fa0be83e0 0xfffe00fffffc01ff 0x02a1803fe0ff83e0

def z806 : W := mkw 0x000000fc7393a000 0x0446df40007dfc00 0x000000fffffffe00 0x04c2ffc000fffc00

def z807 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xc00e000000000000 0x000cf9fce0000000

def z808 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xffffffffffffffff 0xffff863fffffffff

def z809 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffff000003f800 0xff0fffffff00701c

def z810 : W := mkw 0x7fdbfd028c245b6d 0xa38020bfff8203de 0xffffff00000001ff 0xf330003fff0003ff

def z811 : W := mkw 0xa73400030c6801d0 0x0aaf9e6fa08203e0 0xfffe0000000001ff 0x0e2fffffe00003e0

def z812 : W := mkw 0x271400d24e280150 0x082f800fa03e81c0 0xfffe00fffffc001c 0x0a8f803fe0ff8180

def z813 : W := mkw 0x39c9d80820021008 0x890fbedf7f001004 0xffffff0000003800 0x1f0fffffff00300c

def z814 : W := mkw 0x82300041046000c0 0x0a89002980a60360 0xc1fe00ff83fc01e3 0x0aad803de0f78260

def z815 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffff007c00381c 0x1f0fffffff08318c

def z816 : W := mkw 0x210000fc7393a000 0x0c4fdf49207dfc00 0x01fe00fffffffe00 0x0ccfffc1e0fffc00

def z817 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x000000fffffffffc 0xfccfffc000ffff9c

def z818 : W := mkw 0xc0202061804040a0 0x0e89603910e44230 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z819 : W := mkw 0x3949500000000000 0x0106acd67e000000 0xffffff0000000000 0x0f0fffffff000000

def z820 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffffe003e3c600 0x0fcfffffff044c00

def z821 : W := mkw 0xc0a0a20190c0c4a2 0x4280213911812a31 0xc1f1e3e07fffffe3 0xeff387fd130ffe73

def z822 : W := mkw 0x58c3ef2cb187de2f 0xe4007f905f417c1f 0x0001ff000003fe00 0xf5507fc01f007c1f

def z823 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe001cfffc03f81c 0x1c8e7c3e0cf8718c

def z824 : W := mkw 0x000000f862020000 0x0c0fde40007cd000 0x000000fffffff800 0x0c8fffc000fff000

def z825 : W := mkw 0xf9697265814144a2 0x4786cce66ee44631 0x3e0e1cff83e3c7e3 0xe0f285c2ecf44e73

def z826 : W := mkw 0x39cbd50000040a05 0x290fbedf7f00000a 0xffffff0000000000 0xff1fffffff00001f

def z827 : W := mkw 0xb73d10d34e6801d0 0x0baf8c6fa4be83e0 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z828 : W := mkw 0x000000745391a000 0x0c49d3400065ec00 0x000000fffffffe00 0x0ccfffc000fffc00

def z829 : W := mkw 0xb9e9d24501410482 0x490fbedf7f240421 0xffffffe003e3c7e3 0xefffffffff044e73

def z830 : W := mkw 0xc0a0a275c35164a2 0x4ec9f27911e4c631 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z831 : W := mkw 0xa33400d1466800d0 0x082f800fa03e8160 0xfffe00fffffc0003 0x0aaf803fe0ff8060

def z832 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f1e31f83e007e3 0xe37d7a3d13f40e73

def z833 : W := mkw 0x18c9d0d042000000 0x090fbed05f3c8000 0x0001fffffffc0000 0x0d8fffc01fff8000

def z834 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffffe07ffc0000 0x0f8fffffff0f8000

def z835 : W := mkw 0x39c9d00000000000 0x01003edf7f000000 0xffffff0000000000 0x0f03ffffff000000

def z836 : W := mkw 0x250000d24a000100 0x0a8f802f20bc8280 0xfffe00fffffc01fc 0x0a8f803fe0ff8380

def z837 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xc1fe00ff83fc01e3 0x0aad803de0f78260

def z838 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x000000fffffc3800 0x088ffdc000ffb000

def z839 : W := mkw 0xe1a0a265814144a2 0x4e89f23931e44631 0xc1ffe3ff83e3c7e3 0xeffdfa3df3f44e73

def z840 : W := mkw 0xa73400d34e6801d0 0x0aaf9e6fa0be83e0 0xfffe00fffffc01ff 0x0aaff83fe0ff83e0

def z841 : W := mkw 0x2180800000000000 0x080fbe5f31000000 0xffffe30000000000 0x0f0ffffff3000000

def z842 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xffffe3ff83e3c7e3 0xeffffa3ff3f44e73

def z843 : W := mkw 0xf3352879e66a50f8 0x8c29ec19b466d174 0x01fffc0003fff803 0xf421fc01fc07f07c

def z844 : W := mkw 0x4212252094a4ca65 0x2680412080c36b5a 0x000000ffffffffff 0xf0f0000000ffffff

def z845 : W := mkw 0x000000ec31838000 0x0c0f5f00007d7c00 0x000000fffffffe00 0x0ccfffc000fffc00

def z846 : W := mkw 0xa3340051466800d0 0x0aaf802fa0a68360 0xfffe00ff83fc01e3 0x0aaf803fe0f78260

def z847 : W := mkw 0x400022fcf393e422 0x4c4fdf40007dfc11 0x000000fffffffe00 0xecdfffc000fffc13

def z848 : W := mkw 0x4290a22485214462 0x4400721091424551 0x3fffe3e07fffc7ff 0xeff3fa03f30fcff3

def z849 : W := mkw 0x540128aaa8025128 0x8686ec7614d85294 0xfe01fcfffc03f9fc 0xfe8efdfe1cf8739c

def z850 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xc1ffff0000000000 0x050dfffdff000000

def z851 : W := mkw 0x1213050014a48a45 0x20062d169403294a 0xfe01fce07fffffff 0xfefe7c3e1c0fffff

def z852 : W := mkw 0x000000fc7393a000 0x04405f40007dfc00 0x000000fffffffe00 0x0cc3ffc000fffc00

def z853 : W := mkw 0x39c9d08820020000 0x090fbedf7f181000 0xffffff007c003800 0x0f0fffffff083000

def z854 : W := mkw 0x5001202080004020 0x06866c3614c04210 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z855 : W := mkw 0xb9e9d24501410482 0x490fbedf7f240421 0xffffff0000000000 0x0f0fffffff000000

def z856 : W := mkw 0x750528baea0a5138 0x86a6ec3634d8d294 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z857 : W := mkw 0xb9e9d20100400482 0x490fbedf7f000021 0xffffff0000000003 0x0f3fffffff000063

def z858 : W := mkw 0xa73400d34e6801d0 0x0aaf926fa0be83e0 0xfffe00fffffc01ff 0x0aaf83ffe0ff83e0

def z859 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfe0e00fffffc01ff 0x00ae803ee0ff83e0

def z860 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f003ff83e007e3 0x0bfd7a3d03f40e63

def z861 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x0001e0ffffffffe0 0xeecfffc010fffe10

def z862 : W := mkw 0x8020006501410080 0x0e89522900e44620 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z863 : W := mkw 0xa3300041046000c0 0x0a8f802fa0a60360 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z864 : W := mkw 0xc6322fefbde7dfef 0xe680412080ff7fff 0x000000ffffffffff 0xf0f0000000ffffff

def z865 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffe1cfffffc39ff 0x1aaf843fecffb3ec

def z866 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe01fcfffc03f9fc 0xfe8ffffe1cf8739c

def z867 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x000000fffffc0600 0x08cffbc000ff8c00

def z868 : W := mkw 0x000000b87292a000 0x0446cd400059f800 0x0000001ffc1c3800 0x000efdc000fbb000

def z869 : W := mkw 0xa7b480d34e6801d0 0x0aaf922fa1be83e0 0xfffe03fffffc01ff 0x0baf823fe3ff83e0

def z870 : W := mkw 0xe73422d3ce6845f2 0x4aaf802fa0be83f1 0xfffe00fffffc01ff 0xeabf803fe0ff83f3

def z871 : W := mkw 0x39c9d00000000000 0x0106bedf7f000000 0xffffff0000000000 0x0702ffffff000000

def z872 : W := mkw 0x000000fc7393a000 0x0c49d340007dfc00 0x000000fffffffe00 0x0ccdfbc000fffc00

def z873 : W := mkw 0xb73508d34e6811d8 0x8aaf802fa4be83e4 0xfffe1cfffffc01ff 0x1aaf803fecff83ec

def z874 : W := mkw 0x39c9d09042000000 0x090fbedf7f188000 0xffffff007c1c0000 0x0f0fffffff0b8000

def z875 : W := mkw 0x18c1c00000000000 0x080f3e9f5f000000 0xffffff0000000000 0x0f0fffffff000000

def z876 : W := mkw 0x271400924e280150 0x02a68026a09a83c0 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z877 : W := mkw 0x39c9d0fc7393a000 0x0540619f7f7dfc00 0xfffffffffffffe00 0x03c0003ffffffc00

def z878 : W := mkw 0xb9e9d04100400080 0x090fbedf7f240020 0xffffff0003e00003 0x0f2fffffff040060

def z879 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x3e001cfffffffe1c 0x1ccfffc20cfffd8c

def z880 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f1e3ff83e3c7e3 0xeffffffd13f44e73

def z881 : W := mkw 0x061000820c200140 0x02860026809a03c0 0xfe0e00fffc1c01fc 0x0a8e803ee0fb8380

def z882 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffffe07c03f800 0x0f8fffffff087000

def z883 : W := mkw 0xa73400d34e6801d0 0x0aaf8c2fa0be83e0 0xfffe00fffffc01ff 0x0eaffc3fe0ff83e0

def z884 : W := mkw 0x4c4068aaa8025128 0x868040a04ad85294 0x3ffffffffc03f9fc 0xff8387c3fff8739c

def z885 : W := mkw 0xa73408db6e6a11d8 0x8aaf802fa0be93e4 0xfffe00fffffc39ff 0x1aaf803fe0ffb3ec

def z886 : W := mkw 0x271400924e280150 0x02a68026a09a83c0 0xfe0e001ffc1c001c 0x000e803ee0fb8180

def z887 : W := mkw 0x0000006411818000 0x0c0fdf4000656c00 0x000000fffffffe00 0x0ccfffc000fffc00

def z888 : W := mkw 0x39c9d08000000000 0x090fbedf7f180000 0xfffffffffc000000 0x0f8ffffffff80000

def z889 : W := mkw 0x54012856db91f128 0x8ac9b37614a5ae94 0xfe01fc0003fc07fc 0xf24183fe1c078f9c

def z890 : W := mkw 0x4080a22481014422 0x4680723011c04611 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z891 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f1e3ff83e3c7e3 0xe3fc783d13f44e73

def z892 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffff00000001e3 0xef3fffffff000273

def z893 : W := mkw 0x58cbf7249185ce27 0x65007fd05f416c1b 0x0001ff000003fe00 0xf5507fc01f007c1f

def z894 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x0000001f83fc0600 0x0c4fffc000f78c00

def z895 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffe03fffffc07ff 0x0bff823fe3ff8fe3

def z896 : W := mkw 0xc6362dfbfeeedbfd 0xa6a0412080fffbfe 0x000000ffffffffff 0xf0f0000000ffffff

def z897 : W := mkw 0x50012828a0025028 0x86806c3014c05214 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z898 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xfff1ffff83e3c7ff 0xfffd7a3f1ff44fff

def z899 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffe00ffffffc7ff 0x0eef823fe0ffcfe0

def z900 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xc1fe00fffffc01ff 0x00ad803de0ff83e0

def z901 : W := mkw 0x58c9f22cb193e422 0x45407fd05f417c11 0x0001ff000003fe00 0xe5507fc01f007c13

def z902 : W := mkw 0xe1a4a275c34944b2 0x4ea9f23931e4c631 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z903 : W := mkw 0x80a082fd73d3a482 0x4c4fdf49017dfc21 0x01f1e3ffffffffe3 0xefffffc113fffe73

def z904 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x0001e3fffffffe00 0xeddfffc013fffc13

def z905 : W := mkw 0x3949500000000000 0x090facdf7e000000 0xfffffc0000000000 0x0e0ffdfffc000000

def z906 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffe00fffffc01ff 0x0eaf87ffe0ff83e0

def z907 : W := mkw 0x271400d24e280150 0x0aaf8026a0be83c0 0xfe0e00fffffc01fc 0x0a8f803ee0ff8380

def z908 : W := mkw 0x000000d052808000 0x080f9f40003da800 0x000000fffffffe00 0x0ccfffc000fffc00

def z909 : W := mkw 0xff776d038c6c5bfd 0xa2a020bffe8203fe 0xffffff00000001ff 0xf330003fff0003ff

def z910 : W := mkw 0xa3340051466800d0 0x0aa98029a0a68360 0xc1fe001f83fc0003 0x002d803de0f78060

def z911 : W := mkw 0x8af2c75557f5aec7 0x684993c9cb27ad6b 0x01fe030003fc0603 0x017183c1e3078c63

def z912 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe001cfffc0039fc 0x1a8e7c3e0cf8338c

def z913 : W := mkw 0x1841400000000000 0x00062c965e000000 0xfe0ffc0000000000 0x0e0efdfefc000000

def z914 : W := mkw 0x750938aaa8025128 0x8786ec7634d85294 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z915 : W := mkw 0x1841400000000000 0x080fbed65e000000 0xffffff0000000000 0x0f0fffffff000000

def z916 : W := mkw 0x46122dfeffb7fb6d 0xa6c0412080ffffde 0x000000ffffffffff 0xf0f0000000ffffff

def z917 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x0000001ffffc3e00 0x004fffc000ffbc00

def z918 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xc1ffe30000000000 0x0f0dfbfdf3000000

def z919 : W := mkw 0x000000fc7393a000 0x0446cd40007dfc00 0x000000fffffffe00 0x0ccefdc000fffc00

def z920 : W := mkw 0x39c9d00000000000 0x0106acdf7f000000 0xffffff0000000000 0x0f0efdffff000000

def z921 : W := mkw 0x863605ff7fffabd5 0x26e0412080ffffea 0x000000ffffffffff 0xf0f0000000ffffff

def z922 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f003ff83e3c603 0x0dfd7a3d03f44c63

def z923 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xfe0e1c0000000000 0x0c0ffffeec000000

def z924 : W := mkw 0x540128baea025128 0x8686ec3614d8d294 0xfe01fcfffc1ff9fc 0xfe8efc3e1cfbf39c

def z925 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffffe07fe3ffff 0xffffffffff0c7fff

def z926 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffff0000000000 0x030dfbffff000000

def z927 : W := mkw 0x231000d046200040 0x080f800fa03e8140 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z928 : W := mkw 0xabfed55156ec8ad5 0x292993c9eb27a96a 0x01fe030003fc0603 0x017183c1e3078c63

def z929 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffffcfffffc01ff 0xfaaf803ffcff83fc

def z930 : W := mkw 0x0a5245a824260a45 0x24064c80ca5a514a 0x3ffffffffc03f9ff 0xffbe7c03fff873ff

def z931 : W := mkw 0x39c9d00000000000 0x01063edf7f000000 0xffffff0000000000 0x0f0e7fffff000000

def z932 : W := mkw 0x5401282aa8025128 0x86806c3614c05294 0xfe01fcff8003f9fc 0xfe8c7c3e1cf0739c

def z933 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x0000001ffc1c3800 0x0c0fffc000fbb000

def z934 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xfe0ffc0000000000 0x0e0efdfefc000000

def z935 : W := mkw 0x008080fc7393a000 0x0c4fdf49017dfc00 0x01f003fffffffe00 0x0dcfffc103fffc00

def z936 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f1e3ffffffc7e3 0xeffffa3d13ffce73

def z937 : W := mkw 0xab76455557fdaad5 0x286993c9ea27ad6a 0x01fe030003fc0603 0x017183c1e3078c63

def z938 : W := mkw 0x5e536daabca6db6d 0xa6866db6dedb7bde 0xc1fe031f83fc0603 0x017dfbfde3f78c63

def z939 : W := mkw 0xa73400d34e6801d0 0x02a6002fa0be83e0 0xfffe00fffffc01ff 0x0aae003fe0ff83e0

def z940 : W := mkw 0x39c9d09862122000 0x094fbedf7f189000 0xffffff0000000000 0x0f0fffffff000000

def z941 : W := mkw 0xa73400430c6801d0 0x0aa9002fa0a603e0 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z942 : W := mkw 0x3dc9d80208001108 0x890fbedf7f000084 0xffffff000000001c 0x1f0fffffff00018c

def z943 : W := mkw 0x39c9d04000000000 0x090fbedf7f240000 0xffffffff83e00000 0x0f8ffffffff40000

def z944 : W := mkw 0xa73400d34e6801d0 0x0aa98029a0be83e0 0xc1fe00fffffc01ff 0x0aad803de0ff83e0

def z945 : W := mkw 0x0000002010808000 0x0400410000416800 0x000000fffffffe00 0x0ccfffc000fffc00

def z946 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffffcfffffc01ff 0x0eaf843ffcff83e0

def z947 : W := mkw 0x3101000000000000 0x080fbe5f34000000 0xfffffc0000000000 0x0e0ffffffc000000

def z948 : W := mkw 0x79c9f80080005028 0x890fbedf7f000014 0xffffff0000000000 0xff0fffffff00001c

def z949 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe01fffffc03fffc 0xffde7e3e1ff87f9f

def z950 : W := mkw 0x061000d24e200140 0x0a8f802680be83c0 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z951 : W := mkw 0x1e534d9a7eb6bb4d 0xa0468dc6ce1bb9ce 0x3e0e1c007c1c381c 0x100285c2ec0bb18c

def z952 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffe00ffffffc7ff 0xeaff803fe0ffcff3

def z953 : W := mkw 0x040000fe7b93a100 0x0c4fdf46007dfc80 0x3e0000fffffffe1c 0x0ccfffc200fffd80

def z954 : W := mkw 0xcaf2e76595e5cee7 0x6e8973b9dbe76f7b 0xfe0e1c1ffc1c381c 0x100efdfeecfbb18c

def z955 : W := mkw 0x000000745391a000 0x0c4fdf400065ec00 0x000000ff83ffc600 0x0ccfffc000f7cc00

def z956 : W := mkw 0xa3340051466800d0 0x0aa98029a0a68360 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z957 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffe001f83fc01ff 0x022d803fe0f783e0

def z958 : W := mkw 0xa7b482d74f6905d2 0x4aaf922fa1be87e1 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z959 : W := mkw 0xa73400d34e6801d0 0x0aaf922fa0be83e0 0xfffe00fffffc01ff 0x0eaffa3fe0ff83e0

def z960 : W := mkw 0x0000006411818000 0x0c09530000656c00 0x000000ff83ffc600 0x0ccdfbc000f7cc00

def z961 : W := mkw 0x802002fd73d3a482 0x4c4fdf40007dfc21 0x000000fffffffe03 0x0cffffc000fffc63

def z962 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xc00e001f801c0000 0x000c803ce0f38000

def z963 : W := mkw 0xd4212aaba84255aa 0xc6866c3614d852b5 0xfe01fcfffc03f9ff 0xfebe7c3e1cf873ff

def z964 : W := mkw 0x2940400000000000 0x080f9ecf6a000000 0xffffff0000000000 0x0f0fffffff000000

def z965 : W := mkw 0xc63627f7dfedcff7 0x66a0412080ffeffb 0x000000ffffffffff 0xf0f0000000ffffff

def z966 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xfffe1c0000000000 0x0a0ffdffec000000

def z967 : W := mkw 0xeff6e7038c6c4ff7 0x62a020bffb8203fb 0xffffff00000001ff 0xf330003fff0003ff

def z968 : W := mkw 0x0000006c3193a000 0x0c495f4000657c00 0x000000fffffffe00 0x0ccfffc000fffc00

def z969 : W := mkw 0x39c9d00000000000 0x0909b2df7f000000 0xffffff0000000000 0x0f0dfbffff000000

def z970 : W := mkw 0x2100002c3193a000 0x0c4fdf4f20417c00 0xfffe00000003fe00 0x0e4fffffe0007c00

def z971 : W := mkw 0xa73400d34e6801d0 0x02a68026a0be83e0 0xfe0e00fffffc01ff 0x0aae803ee0ff83e0

def z972 : W := mkw 0x0a52456405250a45 0x2c095280ca66454a 0x3fffffff83e3c7ff 0xfffd7a03fff44fff

def z973 : W := mkw 0x29c0c00000000000 0x080fb29f7b000000 0xffffff0000000000 0x0f0fffffff000000

def z974 : W := mkw 0x3dc9d88a28021108 0x890fbedf7f181084 0xffffff0000000000 0x0f0fffffff000000

def z975 : W := mkw 0x750128aaa8025128 0x8686ec3634d85294 0xfe0ffcfffc03f9fc 0xfe8efc3efcf8739c

def z976 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f1e31f83e00603 0x0f7d7a3d13f40c63

def z977 : W := mkw 0x140108fe7b93b108 0x8c4fdf46047dfc84 0x3e01fcfffffffffc 0xfecfffc21cffff9c

def z978 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfff1fffffc03f9ff 0xffbe7c3f1ff873ff

def z979 : W := mkw 0x80a0826501410482 0x4e89522901e44621 0xc1f003ff83e3c7e3 0x0ffd7a3d03f44e63

def z980 : W := mkw 0xa73402d74f6905d2 0x4aaf802fa0be87e1 0xfffe00fffffc07ff 0x0aff803fe0ff8fe3

def z981 : W := mkw 0x000000fc63132000 0x0c4fde40007cd400 0x000000fffffc0000 0x0c8fffc000ff8000

def z982 : W := mkw 0x3dc9d08208000100 0x090fbedf7f180080 0xffffff007c00001c 0x0f0fffffff080180

def z983 : W := mkw 0xc0a0a265814144a2 0x4680603911e44631 0xc1f1e3ff83e3c7e3 0xeffc783d13f44e73

def z984 : W := mkw 0xc0a0a265814144a2 0x4680723011e44631 0xc001e3ff83e3c7e3 0xeffc7a3c13f44e73

def z985 : W := mkw 0x540128baea127128 0x86c6ec7614d8d294 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z986 : W := mkw 0xa73400d74f6901d0 0x0aaf922fa0be87e0 0xfffe00fffffc07ff 0x0aef823fe0ff8fe0

def z987 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffe001ffc1c001c 0x0a0f803fe0fb8180

def z988 : W := mkw 0x80a0826501410482 0x4c09721911644421 0xc1f1e3ff83e3c603 0x0ffd7a3d13f44c63

def z989 : W := mkw 0x29c8d00000000000 0x090fb2df7b000000 0xffffe30000000000 0x0f0ffbfff3000000

def z990 : W := mkw 0x58c9f82cb193f028 0x85407fd05f417c14 0x0001ff000003fe00 0xf5407fc01f007c1c

def z991 : W := mkw 0x000000b87292a000 0x0446cd400059f800 0x000000fffffffe00 0x0ccfffc000fffc00

def z992 : W := mkw 0x250400fe7b9ba110 0x0c6fdf46207dfc80 0x000000fffffffe00 0x0ccfffc000fffc00

def z993 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f1e31f83e3c603 0xe57d7a3d13f44c73

def z994 : W := mkw 0xd0a1aa65814154aa 0xce89723915e44635 0xc1f1ffff83e3c7e3 0xfffd7a3d1ff44e7f

def z995 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x01f1e3fffffffe00 0x0fcfffc113fffc00

def z996 : W := mkw 0x1401088a28021108 0x80060c0604181084 0x3ff1ffe07fe3ffff 0xfff306031f0c7fff

def z997 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe001cfffc03f9fc 0xf08e7c3e0cf8739c

def z998 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x0000001f801c0000 0x000cf9c000f38000

def z999 : W := mkw 0x210000fc7393a000 0x0c4fc10f207dfc00 0xfffe00fffffffe00 0x0acf803fe0fffc00

def z1000 : W := mkw 0x000000bc7393a000 0x0446df400059fc00 0x000000fffc1ffe00 0x0cceffc000fbfc00

def z1001 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffe00fffffff9ff 0x0eaf843fe0fff3e0

def z1002 : W := mkw 0xa73400d34e6801d0 0x0aa9002fa0be83e0 0xfffe00fffffc01ff 0x0aad003fe0ff83e0

def z1003 : W := mkw 0x1401008208000100 0x02862c3614980280 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z1004 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfff1fffffc03f9fc 0xff8f7e3f1ff8739c

def z1005 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfffffcfffc03f9fc 0xfe8ffc3ffcf8739c

def z1006 : W := mkw 0x000000f453818000 0x0c0fd300007dec00 0x000000fffffffe00 0x0ccfffc000fffc00

def z1007 : W := mkw 0xc0a0aa6da14354aa 0xce89723911e45635 0xc1f1e3ff83e3ffe3 0xfffd7a3d13f47e7f

def z1008 : W := mkw 0x39c9d00000000000 0x0909329f7f000000 0xffffff0000000000 0x0f0fffffff000000

def z1009 : W := mkw 0xa12000d142400080 0x0a8f802f20bc8220 0xfffe00fffffc01e3 0x0aaf803fe0ff8260

def z1010 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xffffe3fffffc01ff 0x0faf823ff3ff83e0

def z1011 : W := mkw 0xabfad74515e58ec7 0x690993c9eb272d6b 0x01fe030003fc0603 0x017183c1e3078c63

def z1012 : W := mkw 0xa52400d34a480190 0x0aaf802f20bc82a0 0xfffe00fffffc0000 0x0a8f803fe0ff8000

def z1013 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x000000fffffffe00 0x04cc7fc000fffc00

def z1014 : W := mkw 0x0080806401010000 0x0c09721911644400 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z1015 : W := mkw 0xfffdf8038c6851f8 0x83a020bfff8203f4 0xffffff00000001ff 0xf320003fff0003fc

def z1016 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xc1fe00fffffc0003 0x08af803de0ff8060

def z1017 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffffe00003c1e0 0xef8fffffff004210

def z1018 : W := mkw 0x540128029880d128 0x8280213614812a94 0xfe01fce07ffffffc 0xfec387fe1c0fff9c

def z1019 : W := mkw 0x140108fe7b93b108 0x8c4fdf46047dfc84 0x000000fffffffe00 0x0ccfffc000fffc00

def z1020 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe01fc1ffc00381c 0x1e0e7c3e1cf8318c

def z1021 : W := mkw 0x18c9d00000000000 0x01063ed65f000000 0xffffff0000000000 0x0f0fffffff000000

def z1022 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffffe07c0001fc 0x0f8fffffff080380

def z1023 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xfff1e3ffffe3c7ff 0xefff7a3f13fc4ff3

def z1024 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f1ffff83e3ffe3 0xfffd7e3d1ff47e7f

def z1025 : W := mkw 0x39c9d00000000000 0x0909bed97f000000 0xc1ffff0000000000 0x0f0dfffdff000000

def z1026 : W := mkw 0xa73400d34e6801d0 0x02a0002fa0be83e0 0xfffe00fffffc01ff 0x0aa3803fe0ff83e0

def z1027 : W := mkw 0x79c9f20080004422 0x490fbedf7f000011 0xffffff0000000000 0xef1fffffff000013

def z1028 : W := mkw 0x210000fc7393a000 0x0c4fdf46207dfc00 0x3e0e00fffffffe00 0x0ccfffc2e0fffc00

def z1029 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc1f1e31f8003c7e3 0xe77c7a3d13f04e73

def z1030 : W := mkw 0x2bdad55457b5aa45 0x294993c9eb27ad4a 0x01fe030003fc0603 0x017183c1e3078c63

def z1031 : W := mkw 0x39c9d05042000000 0x090fbedf7f248000 0xffffff0003fc0000 0x0f0fffffff078000

def z1032 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x3e01fcfffffffe00 0x0ecfffc21cfffc00

def z1033 : W := mkw 0x48c2e7249185ce27 0x640073905b416c1b 0x0001e3000003c600 0xe5507bc013004c13

def z1034 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x000000ffffffffe3 0xecffffc000fffe73

def z1035 : W := mkw 0xc23227fdf7f7eee7 0x66c0412080ffff7b 0x000000ffffffffff 0xf0f0000000ffffff

def z1036 : W := mkw 0xa73400db6e6a01d0 0x0aaf8c2fa0be93e0 0xfffe00fffffc39ff 0x0aaf843fe0ffb3e0

def z1037 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffff0000000000 0x070c7fffff000000

def z1038 : W := mkw 0x000000f45391a000 0x0c4fd340007dec00 0x000000ffffffc600 0x0ccffbc000ffcc00

def z1039 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffffe003e001e3 0x0fafffffff040260

def z1040 : W := mkw 0x52112828a4225068 0x84006c1094425154 0x3ffffce07ffff9ff 0xfea3fc03fc0ff3fc

def z1041 : W := mkw 0x39c9d00000000000 0x0909bedf7f000000 0xffffff0000000000 0x0701ffffff000000

def z1042 : W := mkw 0xa12400fd73dba090 0x0c6fdf49207dfc20 0x000000fffffffe00 0x0ccfffc000fffc00

def z1043 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x0001fcfffffffe00 0xfccfffc01cfffc1c

def z1044 : W := mkw 0x863000c30c6001c0 0x0a8f002f80be03e0 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z1045 : W := mkw 0xc0a0a265814144a2 0x4e89723911e44631 0xc001e3ff83e3c7e3 0xe5fc7a3c13f44e73

def z1046 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xfe0fff0000000000 0x050efffeff000000

def z1047 : W := mkw 0x0210000004200040 0x0280002080820340 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z1048 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffff00000001fc 0xff0fffffff00039c

def z1049 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xffffe3fffffc01ff 0xebbf803ff3ff83f3

def z1050 : W := mkw 0x000000fc7393a000 0x0c495f40007dfc00 0x000000fffffffe00 0x0ccd7fc000fffc00

def z1051 : W := mkw 0xfbfbf70184644ee7 0x638020bfff82037b 0xffffff00000001ff 0xf330003fff0003ff

def z1052 : W := mkw 0x80a0824501410482 0x4809120901240421 0x3ff1ffe07fe3ffff 0xfff306031f0c7fff

def z1053 : W := mkw 0x140108aa28021108 0x86864c2604d85284 0xfe001cfffc03f9fc 0x1e8e7c3e0cf8738c

def z1054 : W := mkw 0x5481aaaaa802552a 0xc6866c3615d85295 0xfe01fffffc03f9fc 0xff9e7c3e1ff8739f

def z1055 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x01f003fffffffe03 0x0dffffc103fffc63

def z1056 : W := mkw 0x823000d1466000c0 0x0a8f802980be8360 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z1057 : W := mkw 0x000000a830828000 0x0c0fdf4000597800 0x000000fffffffe00 0x0ccfffc000fffc00

def z1058 : W := mkw 0xc4a0aa67894155aa 0xce89723911e446b5 0xc1f1e3ff83e3c7ff 0xfffd7a3d13f44fff

def z1059 : W := mkw 0xa33400d1466800d0 0x0aaf8029a0be8360 0xc1fe00fffffc01e3 0x0aaf803de0ff8260

def z1060 : W := mkw 0x58cbfd28b086da2d 0xa5007fd05f41781e 0x0001ff000003fe00 0xf5507fc01f007c1f

def z1061 : W := mkw 0x000205fc7397aa05 0x2c4fdf40007dfc0a 0x000000fffffffe00 0xfcdfffc000fffc1f

def z1062 : W := mkw 0xb73508db6e6a11d8 0x8aaf8c2fa4be93e4 0xfffffcfffffff9ff 0xfeaf843ffcfff3fc

def z1063 : W := mkw 0x271000820c200140 0x0a8f802fa09a03c0 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z1064 : W := mkw 0xe1a8b265814144a2 0x4f89f27931e44631 0xc1f1e3ff83e3c7e3 0xeffd7a3d13f44e73

def z1065 : W := mkw 0x3f574d9a7eae9b5d 0xa0268d86ee1bb9ce 0x3e0e1c007c1c381c 0x100285c2ec0bb18c

def z1066 : W := mkw 0xc232276595e5cee7 0x6680412080e76f7b 0x000000ff83ffc7e3 0xe0f0000000f7ce73

def z1067 : W := mkw 0x000000d45391a000 0x084f9f40003dac00 0x000000fffffc0600 0x0ccfffc000ff8c00

def z1068 : W := mkw 0x58436d2cb197fa2d 0xa4407fd05e417c1e 0x0001ff000003fe00 0xf5507fc01f007c1f

def z1069 : W := mkw 0x39c9d04401010000 0x090fbedf7f240400 0xffffff0003e00600 0x0f4fffffff040c00

def z1070 : W := mkw 0x440020a288004120 0x0686603610d84290 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z1071 : W := mkw 0x802000fd73d3a080 0x0c4fdf49007dfc20 0x01f000fffffffe03 0x0cefffc100fffc60

def z1072 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x000000fffffffe00 0x00cefdc000fffc00

def z1073 : W := mkw 0x100108fc7393b008 0x8c4fdf40047dfc04 0x00001cfffffffe00 0x1ccfffc00cfffc0c

def z1074 : W := mkw 0xb9edd05142480090 0x092fbedf7f248020 0xffffff0000000000 0x0f0fffffff000000

def z1075 : W := mkw 0x000000f87292a000 0x0c4fcd40007df800 0x000000fffffff800 0x0c8ffdc000fff000

def z1076 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfe0e00fffffc001c 0x088f803ee0ff8180

def z1077 : W := mkw 0xa73400934e6801d0 0x02a6802fa09a83e0 0xfffe00fffc1c01ff 0x0aae803fe0fb83e0

def z1078 : W := mkw 0x000000fc7393a000 0x0c495300007dfc00 0x000000fffffffe00 0x0ccfffc000fffc00

def z1079 : W := mkw 0x29c8d00000000000 0x0909b2d97b000000 0xc1fe030000000000 0x010dfbfde3000000

def z1080 : W := mkw 0x310910fc7393a000 0x0d4fdf46247dfc00 0x000000fffffffe00 0x0ccfffc000fffc00

def z1081 : W := mkw 0x3941400000000000 0x080fac9f7e000000 0xffffff0000000000 0x0f0fffffff000000

def z1082 : W := mkw 0x000000fc7393a000 0x04465f40007dfc00 0x000000fffffffe00 0x0cce7fc000fffc00

def z1083 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xfffe1f0000000000 0x010fffffef000000

def z1084 : W := mkw 0x000000f872828000 0x0c0fcd00007df800 0x000000fffffffe00 0x0ccfffc000fffc00

def z1085 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe01fc1ffc0039fc 0xf20e7c3e1cf8339c

def z1086 : W := mkw 0xa73400830c6801d0 0x02a6002fa09a03e0 0xfffe00fffffc01ff 0x0aaf803fe0ff83e0

def z1087 : W := mkw 0x540128aaa8025128 0x8680603614d85294 0xfe01fcfffc03f9fc 0xfe8c783e1cf8739c

def z1088 : W := mkw 0xe9e8f265814144a2 0x4f89d2e96be44631 0x01fe03ff83e3c7e3 0xe1f183c1e3f44e73

def z1089 : W := mkw 0x54012aaea903552a 0xc6866c3614d85695 0xfe01fcfffc03fffc 0xfede7c3e1cf87f9f

def z1090 : W := mkw 0x3189900000000000 0x090fbe5f35000000 0xfffe000000000000 0x0e0fffffe0000000

def z1091 : W := mkw 0xabf6c75557ed8ed7 0x68299389eb27ad6b 0x01fe030003fc0603 0x017183c1e3078c63

def z1092 : W := mkw 0x3dcdd0924a080110 0x092fbedf7f188080 0xffffff0000000000 0x0f0fffffff000000

def z1093 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x000000fffc1ff800 0x0c8efdc000fbf000

def z1094 : W := mkw 0x58436d28b086da2d 0xa4006d905e41781e 0x0001fc000003f800 0xf4007dc01c00701c

def z1095 : W := mkw 0x3dc9d88a28021108 0x890fbedf7f181084 0xffffffe07c03f9fc 0xff8fffffff08739c

def z1096 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffe00fffffff9ff 0xfaaf803fe0fff3fc

def z1097 : W := mkw 0x08c0c00000000000 0x080932995b000000 0xc1ffe30000000000 0x0f0dfbfdf3000000

def z1098 : W := mkw 0x39c9d00000000000 0x090fbedf7f000000 0xffffff0000000000 0x030efdffff000000

def z1099 : W := mkw 0x39c9d0d042000000 0x090fbedf7f3c8000 0xffffff1f80000000 0x0f0ffffffff00000

def z1100 : W := mkw 0x0c42458218848b05 0x228601a64a992a8a 0xfe01fffffc03fffc 0xffde07fe1ff87f9f

def z1101 : W := mkw 0xc63428fffffbf1f8 0x86e0412080fffff4 0x000000ffffffffff 0xf0e0000000fffffc

def z1102 : W := mkw 0xc0a0a225814144a2 0x4680723911c04631 0xc1f1e3ff8003c7e3 0xeffc7a3d13f04e73

def z1103 : W := mkw 0x39c9d00000000000 0x09093edf7f000000 0xffffff0000000000 0x0f0d7fffff000000

def z1104 : W := mkw 0x29c8d00000000000 0x0909b2d97b000000 0xffffff0000000000 0x0f0fffffff000000

def z1105 : W := mkw 0x218890fc7393a000 0x0d4fdf49217dfc00 0x000000fffffffe00 0x0ccfffc000fffc00

def z1106 : W := mkw 0x400028fcf393f028 0x8c4fdf40007dfc14 0x000000fffffffe00 0xfccfffc000fffc1c

def z1107 : W := mkw 0x000000d87292a000 0x084f9f40003db800 0x000000fffffc3800 0x0c8fffc000ffb000

def z1108 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe01fc1ffc03f81c 0xf40e7c3e1cf8719c

def z1109 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe01fcfffffff9fc 0xfe8ffc3e1cfff39c

def z1110 : W := mkw 0x29c8d00000000000 0x090f9ecf6b000000 0xfffe030000000000 0x0f0fffffe3000000

def z1111 : W := mkw 0xc0a0a275c34144a2 0x4e89f23911e4c631 0xc1f1e3ff83ffc7e3 0xeffdfa3d13f7ce73

def z1112 : W := mkw 0x18c9d00000000000 0x09093ed95f000000 0xffffff0000000000 0x0f0fffffff000000

def z1113 : W := mkw 0x1401088a28021108 0x82862c3614981284 0xfe01fcfffc0039fc 0x1e8e7c3e1cf8338c

def z1114 : W := mkw 0x48c2e72cb197ee27 0x64407fd05b417c1b 0x0001ff000003fe00 0xf5507fc01f007c1f

def z1115 : W := mkw 0x0292850014a48a45 0x280933199103294a 0xc1f1e3e07fffffff 0xfffd7a3d130fffff

def z1116 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfe0e00fffc1c01fc 0x0a8e803ee0fb8380

def z1117 : W := mkw 0x39c9d05443112000 0x094fbedf7f248400 0xffffff0000000000 0x0f0fffffff000000

def z1118 : W := mkw 0xc63422fffffbe5f2 0x46e0412080fffff1 0x000000ffffffffff 0xe0f0000000fffff3

def z1119 : W := mkw 0x440028aaa8025128 0x8680603010d85294 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z1120 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x000000ff83ffc600 0x0ccdfbc000f7cc00

def z1121 : W := mkw 0x000000fc7393a000 0x0c4fdf46007dfc00 0xfe0000fffffffe00 0x0ecffffe00fffc00

def z1122 : W := mkw 0x3949500000000000 0x0106acd67e000000 0xfe0e1c0000000000 0x000efdfeec000000

def z1123 : W := mkw 0xa73400d34e6801d0 0x0aaf802fa0be83e0 0xfffe00fffffc01ff 0x02ac003fe0ff83e0

def z1124 : W := mkw 0x5401289afa92f128 0x82c6ad761499ba94 0xfe01fc007c1c39fc 0xf20285fe1c0bb39c

def z1125 : W := mkw 0x000000fc7393a000 0x0c4fdf40007dfc00 0x01f000ffffffffe3 0x0eefffc100fffe60

def z1126 : W := mkw 0x46122daabca6db6d 0xa680412080db7bde 0x000000fffc1ff9fc 0xf080000000fbf39c

def z1127 : W := mkw 0x040000aa28020100 0x06864c2600d85280 0xfe01fcfffc03f9fc 0xfe8e7c3e1cf8739c

def z1128 : W := mkw 0x3f5b5d8a3ca69b4d 0xa1068dc6ee1b39ce 0x3e0e1c007c1c381c 0x100285c2ec0bb18c

def z1129 : W := mkw 0xcaf2e70184644ee7 0x628020b9db82037b 0xc1ffe300000001e3 0xe330003df3000273

def z1130 : W := mkw 0x484265209084ca25 0x240061905a41681a 0x0001ff000003fe00 0xf5507fc01f007c1f

def z1131 : W := mkw 0x18cbd52c3197aa05 0x25407fd05f417c0a 0x0001ff000003fe00 0xf5507fc01f007c1f

def z1132 : W := mkw 0xa73400534e6801d0 0x0aa9802fa0a683e0 0xfffe00ff83fc01ff 0x0aad803fe0f783e0

def z1133 : W := mkw 0x540128aaa8025128 0x86866c3614d85294 0xfe01fcffffe3ffff 0xfefe7c3e1cfc7fff

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkA : List (List (List (ℕ × List W))) :=
  [[[(0,[z0,z1,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z8,z5,z6]),(0,[z7,z9,z2,z3,z4,z5,z6]),(0,[z10,z7,z2,z3,z11,z5,z6]),(0,[z7,z2,z12,z3,z13,z5,z6]),(0,[z7,z2,z3,z4,z5,z14,z6]),(0,[z7,z2,z3,z4,z15,z5,z6]),(0,[z7,z2,z3,z4,z5,z16,z6])],[(1,[z7,z2,z3,z4,z8,z6]),(0,[z7,z2,z17,z3,z4,z5,z6]),(0,[z7,z18,z2,z3,z4,z19,z6]),(1,[z7,z2,z3,z4,z20,z6]),(0,[z7,z2,z3,z4,z21,z5,z6]),(0,[z7,z22,z2,z3,z4,z5,z23]),(0,[z7,z2,z24,z3,z4,z5,z6]),(0,[z7,z2,z3,z25,z4,z5,z6])],[(0,[z7,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z26,z3,z4,z5,z6]),(0,[z27,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z28,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z29,z5,z6]),(0,[z30,z2,z3,z4,z31,z5,z6])],[(0,[z7,z2,z32,z3,z4,z5,z6]),(0,[z7,z33,z3,z4,z5,z34,z6])],[(1,[z35,z2,z3,z4,z5,z6]),(0,[z36,z7,z2,z3,z4,z5,z6]),(0,[z7,z37,z2,z3,z4,z6,z38])],[(0,[z7,z2,z3,z4,z5,z6,z39]),(1,[z7,z2,z3,z4,z5,z40]),(0,[z7,z22,z2,z41,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z42,z6]),(0,[z30,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z43,z6])],[(0,[z44,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z45,z6]),(0,[z7,z2,z46,z3,z4,z5,z6]),(0,[z47,z48,z2,z3,z4,z5,z6]),(0,[z49,z7,z2,z3,z4,z50,z6]),(0,[z51,z7,z2,z3,z4,z5,z6])],[(0,[z52,z7,z2,z3,z4,z5,z6]),(0,[z2,z53,z3,z4,z5,z6,z54]),(0,[z55,z7,z2,z3,z4,z5,z6]),(0,[z0,z7,z2,z3,z4,z5,z56]),(0,[z7,z2,z12,z3,z4,z31,z5])]],
   [[(0,[z7,z2,z3,z57,z4,z5,z6]),(0,[z7,z2,z58,z59,z4,z5,z6]),(0,[z7,z2,z3,z60,z4,z5,z6]),(0,[z61,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z12,z62,z4,z5,z6])],[(0,[z63,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z64,z15,z5,z6]),(1,[z65,z2,z3,z4,z5,z6])],[(0,[z7,z2,z66,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z67,z6]),(0,[z7,z2,z3,z68,z4,z5,z6]),(0,[z7,z2,z69,z3,z4,z31,z6])],[(0,[z7,z2,z3,z4,z5,z70,z6]),(0,[z7,z71,z18,z3,z4,z5,z6]),(0,[z7,z2,z72,z3,z4,z5,z6])],[(0,[z52,z7,z53,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z73,z6]),(0,[z7,z2,z3,z4,z5,z6,z74]),(0,[z7,z22,z75,z2,z4,z5,z6]),(0,[z7,z2,z76,z3,z4,z5,z6]),(0,[z7,z2,z3,z77,z4,z5,z6])],[(0,[z7,z2,z3,z78,z5,z6,z79]),(0,[z7,z2,z80,z3,z4,z5,z6]),(0,[z7,z2,z12,z3,z4,z81,z6])],[(0,[z7,z2,z3,z4,z82,z5,z6]),(0,[z7,z83,z2,z3,z4,z5,z6]),(0,[z7,z2,z84,z3,z85,z4,z5])],[(0,[z7,z2,z3,z86,z87,z5,z6])]],
   [[(0,[z7,z2,z88,z3,z4,z5,z6]),(0,[z7,z2,z89,z3,z4,z5,z6])],[(0,[z90,z7,z2,z3,z4,z5,z34]),(0,[z7,z2,z91,z3,z4,z5,z6]),(0,[z7,z2,z3,z92,z4,z5,z6])],[(0,[z93,z10,z2,z3,z4,z5,z6]),(0,[z7,z2,z94,z3,z4,z5,z6]),(0,[z7,z2,z95,z4,z15,z5,z6]),(0,[z7,z2,z3,z4,z96,z5,z6])],[(0,[z97,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z98,z3,z4,z5,z6]),(0,[z99,z7,z2,z3,z4,z5,z6]),(0,[z7,z100,z2,z3,z4,z5,z6]),(0,[z101,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z102,z3,z4,z5,z6])],[(0,[z7,z2,z103,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z104,z5,z6])],[(0,[z7,z2,z3,z105,z4,z5,z6]),(0,[z7,z2,z106,z4,z5,z107,z6]),(0,[z7,z2,z3,z4,z108,z109,z6]),(0,[z7,z37,z2,z3,z86,z5,z6])],[(0,[z93,z7,z1,z3,z4,z5,z6]),(0,[z7,z110,z2,z3,z4,z5,z6]),(0,[z111,z7,z2,z3,z4,z5,z6])],[(0,[z112,z7,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z113,z5,z6]),(0,[z49,z7,z2,z114,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z115]),(0,[z7,z22,z2,z4,z15,z5,z6]),(0,[z7,z2,z3,z4,z5,z116,z6])],[(0,[z49,z7,z2,z3,z13,z5,z6]),(0,[z7,z117,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z118,z5,z6]),(0,[z7,z119,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z120,z5,z6])],[(0,[z7,z2,z3,z4,z5,z121,z6]),(1,[z48,z2,z122,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z123,z6]),(0,[z7,z2,z3,z124,z4,z5,z6]),(0,[z7,z125,z2,z3,z4,z5,z6]),(0,[z7,z126,z2,z3,z4,z5,z6])],[(0,[z93,z2,z53,z3,z4,z5,z6]),(0,[z127,z7,z2,z3,z4,z5,z6]),(0,[z7,z128,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z129,z5,z6]),(0,[z7,z75,z2,z64,z4,z5,z6])],[(0,[z7,z2,z130,z3,z4,z5,z6]),(0,[z7,z2,z131,z3,z4,z5,z6]),(0,[z7,z2,z3,z132,z4,z5,z6]),(1,[z7,z2,z3,z4,z133,z6]),(0,[z7,z2,z3,z134,z4,z5,z6])],[(0,[z10,z7,z2,z3,z135,z5,z6])],[(0,[z7,z2,z3,z136,z4,z5,z6]),(0,[z7,z2,z3,z4,z109,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z137]),(0,[z7,z2,z138,z3,z4,z5,z6]),(0,[z7,z2,z84,z3,z4,z5,z6])]],
   [[(0,[z139,z7,z2,z3,z4,z5,z6]),(0,[z140,z7,z2,z3,z4,z5,z6]),(0,[z7,z141,z2,z3,z4,z5,z6]),(0,[z7,z75,z3,z59,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z142])],[(0,[z7,z2,z143,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z144]),(0,[z7,z2,z3,z4,z5,z145,z6]),(0,[z7,z2,z3,z4,z146,z5,z6]),(0,[z7,z2,z3,z147,z4,z5,z6]),(0,[z7,z2,z3,z148,z4,z5,z6])],[(0,[z7,z2,z3,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z149,z6]),(0,[z0,z2,z3,z4,z5,z6,z54]),(1,[z2,z150,z3,z4,z5,z6]),(0,[z151,z2,z12,z3,z4,z5,z6]),(1,[z7,z2,z152,z4,z5,z6])],[(0,[z153,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z154,z5,z6]),(0,[z7,z2,z4,z108,z5,z155,z6]),(0,[z7,z2,z156,z3,z4,z5,z6])],[(0,[z55,z7,z2,z3,z4,z107,z6])],[(0,[z93,z2,z3,z4,z5,z56,z6]),(0,[z157,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z158]),(0,[z7,z2,z3,z4,z5,z6,z159]),(0,[z90,z7,z2,z160,z4,z5,z6]),(0,[z7,z2,z41,z3,z4,z5,z6]),(1,[z2,z161,z3,z4,z5,z6])],[(0,[z48,z7,z2,z162,z4,z5,z6]),(0,[z163,z7,z2,z3,z4,z5,z6]),(0,[z65,z2,z164,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z165]),(0,[z7,z2,z3,z31,z5,z6,z166]),(0,[z7,z167,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z19,z6,z168]),(0,[z7,z2,z3,z4,z5,z169,z6]),(0,[z7,z170,z2,z3,z4,z5,z6]),(0,[z7,z2,z84,z3,z85,z4,z6])]],
   [[(0,[z7,z2,z171,z3,z4,z5,z6]),(0,[z7,z75,z2,z4,z5,z23,z6]),(0,[z7,z2,z3,z4,z5,z172,z6]),(0,[z7,z2,z3,z173,z4,z5,z6]),(0,[z7,z2,z64,z4,z15,z5,z6]),(0,[z7,z2,z3,z4,z174,z5,z6]),(0,[z7,z2,z175,z4,z31,z5,z6])],[(0,[z7,z2,z3,z4,z176,z5,z6]),(0,[z7,z2,z3,z4,z177,z178,z6]),(0,[z7,z71,z3,z4,z5,z19,z6])],[(0,[z7,z179,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z180,z5,z6]),(0,[z181,z7,z2,z3,z4,z5,z6]),(0,[z49,z182,z2,z3,z4,z5,z6]),(0,[z7,z2,z183,z3,z4,z5,z6]),(0,[z7,z184,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z185,z155,z6]),(0,[z7,z2,z3,z4,z5,z6,z186]),(0,[z7,z2,z58,z3,z4,z5,z187]),(0,[z7,z2,z3,z4,z188,z5,z6]),(0,[z7,z2,z189,z3,z4,z5,z6])],[(1,[z93,z53,z3,z4,z5,z6]),(0,[z7,z190,z2,z3,z4,z5,z6]),(0,[z7,z2,z191,z3,z4,z5,z6])],[],[(0,[z7,z2,z3,z4,z192,z5,z6]),(0,[z7,z2,z193,z3,z4,z5,z6]),(0,[z7,z2,z194,z4,z178,z5,z6])],[(0,[z10,z1,z2,z3,z4,z5,z6]),(0,[z49,z7,z2,z3,z4,z67,z6]),(0,[z7,z2,z4,z15,z5,z23,z6]),(0,[z7,z22,z2,z3,z4,z5,z187])],[(0,[z195,z52,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z196,z6]),(1,[z0,z2,z3,z4,z5,z54]),(0,[z7,z2,z3,z4,z197,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z198])]],
   [[(0,[z7,z2,z3,z178,z5,z6,z166]),(0,[z7,z2,z3,z4,z199,z5,z6])],[(0,[z195,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z150,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z200,z5,z38])],[(0,[z7,z2,z3,z4,z201,z5,z6]),(0,[z7,z202,z2,z3,z4,z5,z6]),(1,[z7,z2,z203,z4,z5,z6]),(0,[z47,z7,z2,z3,z4,z107,z6]),(0,[z7,z2,z3,z4,z5,z204,z6]),(0,[z205,z7,z2,z3,z4,z5,z6]),(0,[z7,z206,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z207,z5,z6]),(0,[z90,z7,z2,z12,z3,z4,z5])],[(1,[z7,z2,z194,z4,z5,z6]),(0,[z7,z2,z208,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z209,z6])],[(0,[z210,z7,z2,z3,z4,z5,z6]),(0,[z7,z71,z2,z3,z4,z200,z6]),(0,[z7,z2,z164,z3,z4,z155,z6])],[(0,[z211,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z212,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z87,z19,z6]),(0,[z90,z7,z2,z3,z4,z20,z6])],[(0,[z213,z7,z2,z3,z4,z5,z6]),(0,[z214,z7,z2,z3,z4,z5,z6]),(0,[z7,z215,z2,z3,z4,z5,z6]),(0,[z7,z216,z2,z64,z4,z5,z6]),(0,[z49,z7,z2,z3,z4,z5,z159]),(0,[z217,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z218,z3,z4,z155,z6]),(0,[z7,z2,z58,z3,z4,z5,z6]),(0,[z7,z2,z219,z3,z4,z5,z6])],[(0,[z220,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z59,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z221]),(0,[z7,z216,z95,z3,z4,z5,z6]),(0,[z90,z7,z3,z4,z5,z6,z79]),(0,[z7,z2,z3,z4,z108,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z6,z222]),(0,[z7,z2,z3,z4,z223,z5,z6])],[(0,[z7,z2,z3,z224,z4,z5,z6]),(0,[z7,z2,z225,z3,z4,z5,z6])],[(0,[z7,z2,z84,z3,z4,z226,z6]),(1,[z151,z2,z3,z4,z5,z6]),(0,[z7,z2,z62,z3,z4,z5,z6])],[(0,[z227,z7,z2,z3,z4,z5,z6]),(0,[z228,z2,z3,z162,z4,z5,z6]),(1,[z7,z2,z229,z4,z5,z6])],[(0,[z49,z7,z230,z3,z4,z5,z6]),(1,[z231,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z232,z4,z5,z6]),(0,[z7,z2,z3,z233,z4,z5,z6]),(0,[z7,z230,z2,z3,z4,z5,z6]),(0,[z7,z2,z64,z3,z15,z5,z6]),(0,[z7,z2,z3,z234,z4,z5,z6])],[(0,[z7,z216,z75,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z235])],[(0,[z7,z2,z3,z4,z5,z6,z236]),(0,[z7,z2,z237,z3,z4,z5,z6]),(0,[z7,z238,z2,z3,z4,z5,z6]),(0,[z7,z2,z239,z3,z4,z5,z6])]],
   [[(0,[z7,z240,z2,z3,z4,z5,z6]),(0,[z7,z241,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z242,z5,z6])],[(0,[z7,z2,z3,z4,z243,z5,z6]),(0,[z228,z2,z3,z4,z109,z5,z6])],[(0,[z7,z216,z2,z4,z5,z23,z6]),(0,[z7,z244,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z85,z4,z200,z5])],[(0,[z7,z2,z3,z4,z5,z6,z245]),(0,[z246,z7,z2,z3,z4,z5,z6])],[(0,[z182,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z247]),(0,[z7,z2,z3,z4,z200,z6,z38])],[(0,[z7,z2,z3,z248,z4,z5,z6]),(0,[z7,z2,z249,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z40,z6]),(0,[z7,z2,z3,z4,z250,z5,z6]),(0,[z7,z33,z2,z3,z251,z4,z5]),(0,[z7,z2,z3,z4,z5,z81,z6])],[(0,[z7,z2,z252,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z253,z5,z6]),(0,[z7,z2,z254,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z255]),(0,[z7,z2,z3,z4,z256,z5,z6]),(0,[z7,z2,z257,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z258])]],
   [[(0,[z2,z53,z3,z4,z11,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z259]),(0,[z7,z18,z2,z3,z4,z5,z6]),(0,[z7,z2,z260,z3,z4,z5,z6]),(0,[z7,z33,z2,z3,z4,z5,z79]),(0,[z7,z261,z2,z3,z4,z5,z6]),(0,[z7,z262,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z263,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z187])],[(0,[z7,z2,z3,z264,z4,z5,z6]),(0,[z7,z265,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z266,z6]),(0,[z7,z37,z2,z3,z4,z87,z6])],[(0,[z267,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z268,z5,z6]),(0,[z7,z269,z2,z3,z4,z5,z6]),(0,[z7,z2,z64,z3,z124,z5,z6]),(0,[z7,z2,z3,z270,z4,z5,z6]),(0,[z7,z2,z3,z4,z271,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z272]),(0,[z7,z2,z3,z4,z273,z5,z6]),(0,[z7,z2,z175,z3,z4,z5,z6]),(0,[z7,z2,z3,z85,z4,z6,z38])],[(0,[z7,z2,z53,z3,z4,z5,z6]),(0,[z7,z2,z274,z3,z4,z5,z6]),(0,[z7,z2,z275,z3,z4,z5,z6])],[(0,[z7,z2,z276,z3,z4,z5,z6]),(0,[z7,z2,z12,z3,z4,z5,z6]),(1,[z7,z2,z4,z5,z277,z6]),(0,[z7,z2,z3,z4,z278,z5,z6])],[(0,[z7,z2,z218,z122,z4,z5,z6]),(0,[z7,z279,z2,z3,z4,z5,z6]),(0,[z10,z2,z3,z4,z11,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z280]),(0,[z7,z2,z281,z3,z4,z5,z6]),(0,[z7,z2,z282,z3,z4,z5,z6]),(0,[z7,z283,z2,z3,z4,z5,z6]),(0,[z7,z2,z284,z3,z4,z5,z6]),(0,[z7,z2,z164,z3,z4,z108,z6]),(0,[z7,z2,z3,z285,z4,z5,z6]),(0,[z7,z2,z3,z85,z4,z87,z6]),(0,[z7,z2,z286,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z287,z6]),(0,[z7,z2,z59,z4,z15,z5,z6]),(0,[z7,z2,z3,z4,z288,z5,z6]),(0,[z7,z2,z3,z86,z4,z6,z38]),(0,[z7,z2,z3,z4,z289,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z4,z5,z6]),(0,[z7,z2,z3,z135,z4,z5,z6]),(0,[z10,z2,z3,z4,z5,z6,z54]),(0,[z2,z3,z4,z109,z5,z107,z6]),(0,[z7,z3,z13,z4,z178,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z290]),(0,[z7,z18,z2,z3,z85,z4,z6]),(0,[z7,z2,z218,z3,z4,z108,z6]),(1,[z7,z37,z2,z3,z6,z168]),(0,[z291,z7,z2,z3,z4,z5,z6])],[(0,[z93,z7,z53,z3,z4,z5,z6]),(0,[z7,z2,z3,z292,z4,z5,z6]),(0,[z7,z2,z3,z293,z4,z5,z6])],[(1,[z7,z2,z294,z4,z5,z6]),(0,[z7,z2,z295,z3,z4,z5,z6]),(0,[z7,z2,z3,z86,z4,z87,z6])],[(0,[z296,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z297,z4,z5,z6]),(0,[z298,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z299,z4,z5,z6]),(0,[z7,z2,z3,z4,z20,z5,z6]),(0,[z7,z2,z164,z4,z5,z155,z6]),(0,[z7,z2,z12,z3,z4,z5,z166]),(0,[z7,z2,z3,z4,z31,z43,z6])],[(0,[z48,z2,z3,z4,z5,z107,z6]),(0,[z300,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z6]),(0,[z7,z2,z3,z4,z301,z5,z6]),(1,[z7,z2,z4,z5,z6,z302]),(0,[z7,z2,z3,z4,z303,z5,z6]),(0,[z7,z304,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z305,z5,z6]),(0,[z7,z2,z3,z306,z4,z5,z6]),(0,[z7,z35,z2,z3,z4,z5,z6])],[(0,[z7,z2,z95,z58,z4,z5,z6]),(0,[z307,z7,z2,z3,z4,z5,z6]),(0,[z231,z2,z3,z4,z178,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z308]),(0,[z7,z2,z3,z4,z5,z309,z6])]],
   [[(0,[z7,z310,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z50,z5,z6]),(0,[z7,z2,z64,z41,z4,z5,z6]),(0,[z7,z2,z164,z3,z4,z5,z6]),(0,[z7,z2,z311,z3,z4,z5,z6]),(0,[z7,z312,z2,z3,z4,z5,z6])],[(1,[z7,z2,z3,z4,z177,z6]),(0,[z7,z2,z3,z4,z5,z313,z6])],[(0,[z7,z2,z218,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z314,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z315])],[(0,[z228,z7,z2,z122,z4,z5,z6]),(1,[z7,z2,z66,z3,z4,z6]),(0,[z7,z2,z3,z4,z5,z316,z6]),(0,[z7,z2,z3,z4,z5,z317,z6]),(0,[z195,z0,z2,z3,z4,z5,z6]),(0,[z7,z2,z95,z4,z5,z6,z187]),(0,[z90,z7,z2,z3,z318,z5,z6]),(0,[z7,z2,z3,z4,z319,z5,z6]),(0,[z7,z320,z2,z3,z4,z5,z6])],[(0,[z47,z55,z2,z3,z4,z5,z6]),(1,[z49,z7,z3,z178,z5,z6]),(0,[z7,z2,z3,z321,z4,z5,z6]),(0,[z322,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z166])],[(0,[z323,z52,z2,z3,z4,z5,z6]),(0,[z7,z22,z2,z58,z4,z5,z6])],[(0,[z324,z7,z2,z3,z4,z5,z6]),(0,[z47,z7,z2,z218,z3,z4,z6])],[(0,[z7,z2,z3,z325,z4,z5,z6]),(0,[z2,z3,z135,z4,z5,z6,z54]),(0,[z323,z7,z2,z3,z4,z5,z6]),(0,[z7,z216,z2,z59,z4,z5,z6]),(1,[z326,z2,z3,z4,z5,z6]),(1,[z7,z2,z69,z3,z4,z6])]],
   [[(0,[z7,z327,z2,z3,z4,z5,z6]),(0,[z7,z2,z17,z3,z162,z4,z6]),(0,[z328,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z155,z6]),(0,[z7,z22,z2,z4,z5,z6,z187])],[(0,[z7,z2,z329,z3,z4,z5,z6])],[(0,[z330,z7,z2,z3,z4,z5,z6]),(0,[z0,z2,z3,z4,z11,z5,z6]),(0,[z7,z2,z3,z4,z331,z5,z6]),(0,[z7,z18,z2,z3,z4,z226,z6]),(0,[z332,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z333,z5,z6])],[(0,[z7,z2,z334,z3,z4,z5,z6]),(1,[z7,z2,z335,z3,z4,z5]),(0,[z336,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z78,z5,z6]),(0,[z7,z2,z337,z3,z4,z5,z6]),(0,[z338,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z339,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z340,z6]),(0,[z10,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z341,z4,z5,z6]),(0,[z7,z2,z342,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z343,z6]),(0,[z326,z7,z2,z3,z4,z5,z6])],[(0,[z48,z7,z2,z122,z4,z5,z6]),(0,[z49,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z344,z5,z6]),(1,[z246,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z345,z4,z5,z6]),(0,[z1,z2,z53,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z346,z6]),(0,[z7,z2,z3,z4,z5,z347,z6]),(0,[z228,z7,z2,z3,z4,z5,z6]),(0,[z7,z348,z2,z3,z4,z5,z6])]],
   [[(0,[z2,z3,z4,z11,z5,z56,z6])],[(0,[z7,z2,z66,z3,z162,z4,z6]),(0,[z7,z2,z3,z4,z349,z5,z6]),(0,[z7,z2,z350,z3,z4,z5,z6]),(0,[z7,z2,z351,z3,z4,z5,z6]),(0,[z7,z2,z3,z352,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z353,z6]),(0,[z7,z354,z2,z3,z4,z5,z6]),(0,[z7,z355,z2,z3,z4,z5,z6])],[(0,[z7,z356,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z357]),(0,[z7,z2,z3,z4,z177,z5,z6]),(1,[z7,z2,z3,z318,z5,z6]),(0,[z7,z358,z2,z4,z5,z6,z79]),(0,[z7,z2,z3,z359,z4,z5,z6])],[(0,[z7,z2,z3,z360,z4,z5,z6]),(0,[z1,z2,z3,z135,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z361,z6]),(1,[z7,z2,z276,z4,z5,z6]),(0,[z7,z2,z3,z362,z4,z5,z6])],[(0,[z7,z363,z2,z3,z4,z5,z6]),(0,[z7,z75,z2,z124,z4,z5,z6]),(0,[z7,z2,z364,z3,z4,z5,z6]),(0,[z90,z7,z2,z3,z4,z5,z79])],[(0,[z47,z7,z2,z3,z4,z109,z6]),(0,[z7,z22,z216,z2,z4,z5,z6]),(0,[z7,z230,z3,z13,z4,z5,z6]),(0,[z7,z2,z3,z365,z5,z6,z79]),(0,[z7,z2,z64,z58,z4,z5,z6])],[(1,[z7,z2,z17,z3,z4,z6]),(0,[z7,z2,z3,z366,z4,z5,z6])],[(0,[z7,z2,z3,z4,z31,z5,z34]),(0,[z7,z2,z3,z4,z367,z5,z6]),(0,[z7,z2,z218,z4,z108,z5,z6]),(0,[z7,z37,z2,z3,z5,z6,z168]),(0,[z7,z2,z3,z87,z5,z6,z168])]],
   [[(0,[z1,z2,z3,z4,z5,z56,z6]),(1,[z7,z2,z3,z4,z81,z6])],[(0,[z7,z71,z2,z3,z4,z19,z6]),(1,[z2,z3,z4,z5,z6,z368]),(0,[z7,z2,z64,z4,z5,z6,z187]),(0,[z7,z2,z3,z369,z4,z5,z6]),(0,[z7,z2,z370,z3,z4,z5,z6])],[(0,[z48,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z371,z5,z6])],[(0,[z7,z75,z2,z3,z4,z5,z6]),(0,[z7,z2,z372,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z226,z6,z168]),(1,[z373,z2,z3,z4,z5,z6])],[(0,[z374,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z375,z5,z6]),(1,[z182,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z256,z178,z5,z6]),(0,[z7,z2,z3,z376,z4,z5,z6]),(1,[z7,z22,z2,z4,z5,z187])],[(0,[z228,z7,z2,z3,z4,z8,z6]),(0,[z7,z2,z3,z4,z5,z6,z377])],[(0,[z378,z7,z2,z3,z4,z5,z6]),(1,[z7,z75,z59,z4,z5,z6]),(0,[z7,z2,z3,z379,z4,z178,z5]),(0,[z7,z2,z3,z4,z5,z380,z6]),(0,[z381,z7,z2,z3,z4,z5,z6])],[(0,[z7,z382,z2,z3,z4,z5,z6]),(0,[z7,z2,z95,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z383]),(0,[z7,z2,z161,z3,z4,z5,z6]),(0,[z7,z2,z12,z3,z4,z133,z6])]],
   [[(0,[z7,z384,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z67,z6]),(0,[z7,z2,z385,z3,z4,z5,z6]),(0,[z7,z2,z84,z3,z4,z5,z38])],[(0,[z7,z2,z386,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z387]),(0,[z7,z2,z388,z3,z4,z5,z6])],[(0,[z228,z7,z2,z3,z4,z45,z6]),(0,[z7,z2,z389,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z390]),(0,[z0,z7,z2,z3,z4,z5,z6]),(0,[z90,z7,z2,z3,z4,z123,z6]),(0,[z7,z2,z3,z4,z200,z6,z168])],[(0,[z391,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z318,z4,z5,z6])],[(0,[z228,z7,z2,z4,z108,z5,z6]),(0,[z7,z2,z3,z4,z5,z392,z6]),(0,[z7,z2,z3,z4,z5,z393,z6]),(0,[z7,z2,z394,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z87,z5,z6]),(0,[z7,z2,z12,z152,z4,z5,z6])],[(0,[z395,z7,z2,z3,z4,z5,z6]),(0,[z7,z33,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z396,z4,z5,z6]),(0,[z7,z22,z2,z3,z4,z5,z6]),(0,[z7,z37,z2,z3,z4,z6,z168]),(0,[z7,z2,z3,z4,z397,z5,z6])],[],[(0,[z7,z2,z3,z4,z398,z5,z6]),(0,[z7,z2,z122,z4,z5,z155,z6]),(0,[z195,z2,z3,z135,z4,z5,z6]),(0,[z7,z2,z3,z4,z399,z5,z6]),(0,[z7,z2,z400,z3,z4,z5,z6]),(0,[z401,z7,z2,z3,z4,z5,z6]),(0,[z7,z402,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z403,z4,z5,z6]),(1,[z7,z2,z3,z4,z5,z159]),(0,[z7,z2,z3,z4,z5,z6,z368])],[(1,[z7,z2,z4,z404,z5,z6]),(0,[z7,z2,z3,z405,z4,z5,z6]),(0,[z7,z2,z3,z85,z4,z6,z168])],[(0,[z7,z2,z3,z406,z4,z5,z6]),(0,[z7,z2,z3,z407,z4,z5,z6]),(0,[z408,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z409,z3,z4,z5,z6])],[(0,[z7,z2,z122,z3,z4,z5,z6]),(0,[z410,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z411,z5,z6]),(0,[z412,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z5,z6]),(0,[z7,z2,z413,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z414]),(0,[z7,z2,z3,z86,z4,z6,z168]),(0,[z415,z7,z2,z3,z4,z5,z6])],[(0,[z7,z216,z2,z124,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z416,z6]),(0,[z7,z2,z3,z4,z417,z5,z6])],[(0,[z48,z7,z2,z4,z108,z5,z6]),(0,[z7,z2,z3,z4,z31,z5,z79])]],
   [[(0,[z7,z1,z2,z3,z4,z5,z6]),(0,[z55,z2,z122,z3,z4,z5,z6]),(0,[z7,z75,z2,z59,z4,z5,z6])],[(0,[z418,z7,z2,z3,z4,z5,z6]),(0,[z55,z7,z2,z203,z4,z5,z6]),(1,[z7,z2,z3,z4,z123,z6]),(0,[z7,z2,z4,z5,z6,z302,z79]),(0,[z7,z2,z3,z419,z4,z5,z6]),(0,[z7,z2,z4,z31,z5,z277,z6])],[(0,[z7,z2,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z420,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z421]),(0,[z7,z2,z3,z4,z200,z87,z6])],[],[(0,[z7,z2,z3,z4,z422,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z423])],[(0,[z93,z52,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z424,z4,z5,z6]),(0,[z7,z425,z2,z3,z4,z5,z6]),(0,[z7,z216,z2,z3,z4,z5,z6]),(0,[z7,z2,z41,z95,z4,z5,z6]),(0,[z7,z2,z3,z426,z4,z5,z6]),(0,[z7,z2,z64,z3,z4,z5,z6])],[(0,[z52,z7,z1,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z427,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z428]),(0,[z429,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z430])],[(0,[z93,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z431,z6]),(0,[z7,z18,z3,z4,z226,z5,z6]),(0,[z7,z2,z3,z432,z4,z5,z6])]],
   [[(0,[z7,z71,z2,z3,z4,z226,z6]),(0,[z433,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z434,z5,z6]),(0,[z435,z2,z3,z4,z5,z6,z79])],[(1,[z435,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z365,z5,z6]),(0,[z7,z2,z41,z3,z15,z5,z6]),(1,[z7,z2,z3,z251,z5,z166])],[(0,[z55,z7,z2,z218,z3,z4,z6]),(0,[z7,z2,z3,z436,z4,z5,z6]),(0,[z7,z2,z437,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z50,z6]),(0,[z49,z7,z3,z4,z178,z5,z6]),(0,[z7,z2,z3,z4,z5,z438,z6]),(1,[z30,z2,z3,z4,z5,z6]),(0,[z7,z2,z439,z3,z4,z5,z6])],[(0,[z7,z440,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z441,z4,z5,z6]),(0,[z7,z2,z3,z4,z442,z5,z6]),(0,[z7,z2,z3,z152,z4,z5,z6])],[(0,[z443,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z444,z5,z6]),(0,[z7,z2,z445,z3,z4,z5,z6])],[(0,[z7,z446,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z447,z5,z6]),(0,[z7,z2,z4,z404,z5,z107,z6])],[(0,[z7,z2,z3,z4,z108,z107,z6]),(0,[z7,z448,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z87,z226,z6]),(0,[z7,z2,z41,z4,z5,z23,z6]),(1,[z2,z3,z4,z5,z185,z6]),(0,[z7,z2,z3,z4,z5,z449,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z45,z6]),(0,[z7,z2,z3,z4,z5,z56,z6]),(0,[z7,z2,z3,z450,z4,z5,z6]),(0,[z451,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z59,z4,z5,z6,z187]),(0,[z7,z2,z452,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z34,z6,z79])],[(0,[z7,z2,z3,z4,z5,z6,z453]),(1,[z7,z358,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z454,z6])],[(0,[z7,z2,z3,z4,z455,z5,z6]),(1,[z55,z2,z3,z4,z107,z6]),(0,[z7,z2,z3,z4,z107,z155,z6]),(0,[z90,z246,z2,z3,z4,z5,z6])],[(0,[z7,z456,z2,z3,z4,z5,z6]),(0,[z228,z48,z2,z3,z4,z5,z6])],[],[(0,[z7,z457,z2,z3,z4,z5,z6])],[(0,[z458,z7,z2,z3,z4,z5,z6]),(0,[z7,z459,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z460,z5,z6])],[(0,[z90,z7,z2,z276,z4,z5,z6]),(0,[z7,z2,z461,z3,z4,z5,z6])]],
   [[(0,[z2,z122,z3,z162,z4,z5,z6]),(0,[z2,z3,z135,z4,z11,z5,z6]),(0,[z7,z2,z3,z462,z4,z5,z6])],[(0,[z7,z2,z3,z4,z463,z5,z6]),(1,[z7,z2,z3,z68,z4,z6])],[(0,[z55,z7,z2,z3,z4,z109,z6]),(0,[z7,z2,z3,z4,z5,z107,z6]),(0,[z231,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z84,z3,z86,z4,z6])],[(0,[z464,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z465,z4,z5,z6]),(0,[z7,z2,z3,z466,z4,z5,z6]),(0,[z467,z7,z2,z3,z4,z5,z6])],[(1,[z228,z2,z162,z4,z5,z6]),(0,[z7,z2,z3,z468,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z469,z6]),(0,[z7,z2,z3,z4,z470,z5,z6]),(0,[z7,z2,z3,z471,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z472,z6]),(0,[z7,z2,z3,z203,z4,z5,z6]),(0,[z7,z230,z2,z3,z178,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z473]),(0,[z474,z7,z2,z3,z4,z5,z6])],[(1,[z7,z2,z114,z4,z5,z6]),(0,[z7,z2,z3,z194,z4,z5,z6]),(1,[z7,z2,z3,z4,z319,z6]),(0,[z7,z2,z3,z68,z4,z6,z79]),(0,[z7,z2,z3,z4,z475,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z476]),(0,[z477,z7,z2,z3,z4,z5,z6])],[(0,[z7,z478,z2,z3,z4,z5,z6]),(0,[z47,z2,z3,z162,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z479,z6]),(0,[z7,z2,z3,z4,z5,z480,z6]),(0,[z7,z2,z3,z160,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z481]),(0,[z7,z2,z3,z4,z5,z185,z6]),(0,[z7,z2,z3,z4,z482,z5,z6])],[(0,[z483,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z484,z5,z6]),(0,[z55,z2,z3,z4,z5,z107,z6]),(0,[z7,z2,z3,z4,z485,z5,z6]),(0,[z7,z2,z3,z4,z486,z5,z6]),(0,[z90,z373,z2,z3,z4,z5,z6])]],
   [[(0,[z487,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z11,z5,z6]),(0,[z7,z488,z2,z3,z4,z5,z6]),(0,[z7,z489,z2,z3,z4,z5,z6]),(0,[z7,z490,z2,z3,z4,z5,z6]),(0,[z7,z491,z2,z3,z4,z5,z6])],[(0,[z323,z2,z53,z3,z4,z5,z6]),(0,[z55,z7,z2,z294,z4,z5,z6]),(0,[z7,z230,z2,z3,z31,z5,z6]),(0,[z7,z2,z3,z492,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z54]),(0,[z90,z7,z33,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z493,z5,z6]),(0,[z7,z2,z3,z4,z494,z5,z6])],[(0,[z7,z495,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z496,z6]),(0,[z7,z497,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z31,z273,z5,z6])],[(0,[z7,z2,z3,z498,z4,z5,z6]),(0,[z90,z7,z2,z3,z251,z4,z5]),(0,[z7,z499,z2,z3,z4,z5,z6]),(0,[z7,z500,z2,z3,z4,z5,z6])],[(0,[z323,z2,z3,z135,z4,z5,z6]),(0,[z7,z2,z3,z229,z4,z5,z6])],[(0,[z7,z2,z501,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z502,z5,z6]),(0,[z49,z7,z2,z229,z4,z5,z6]),(0,[z7,z2,z503,z3,z4,z5,z6]),(1,[z7,z2,z62,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z38])],[(0,[z7,z2,z3,z4,z504,z5,z6]),(0,[z7,z2,z505,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z506]),(0,[z7,z358,z2,z3,z4,z5,z6]),(0,[z7,z2,z507,z3,z4,z5,z6])]],
   [[(1,[z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z508,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z509])],[(0,[z7,z2,z3,z510,z4,z5,z6]),(0,[z7,z2,z511,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z512,z5,z6])],[(0,[z7,z513,z2,z3,z4,z5,z6]),(0,[z7,z514,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z515,z6])],[(0,[z195,z10,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z516,z5,z6]),(0,[z323,z7,z2,z3,z4,z5,z54]),(0,[z7,z2,z12,z3,z178,z5,z6]),(0,[z7,z2,z3,z517,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z79,z166]),(0,[z7,z2,z3,z4,z518,z5,z6]),(0,[z7,z519,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z520,z5,z6]),(0,[z7,z2,z3,z4,z5,z521,z6]),(0,[z435,z7,z2,z3,z4,z5,z6])],[]],
   [[(0,[z7,z2,z3,z4,z5,z6,z522]),(0,[z7,z71,z2,z3,z4,z5,z6])],[(0,[z93,z0,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z523,z6]),(0,[z524,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z12,z3,z31,z5,z6])],[(0,[z7,z2,z162,z4,z5,z155,z6]),(0,[z7,z95,z3,z59,z4,z5,z6]),(0,[z49,z35,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z13,z4,z5,z6]),(0,[z7,z2,z3,z4,z525,z5,z6]),(0,[z7,z526,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z527]),(0,[z7,z2,z58,z3,z4,z5,z23])],[(0,[z528,z7,z2,z3,z4,z5,z6]),(0,[z49,z7,z2,z3,z4,z5,z40]),(0,[z7,z2,z3,z4,z529,z5,z6]),(0,[z7,z2,z3,z530,z4,z5,z6]),(0,[z7,z531,z2,z3,z4,z5,z6]),(0,[z7,z532,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z533,z5,z6]),(0,[z7,z534,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z535,z5,z6]),(0,[z7,z2,z536,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z56,z6,z54]),(0,[z7,z2,z3,z537,z4,z5,z6]),(0,[z7,z37,z2,z84,z3,z4,z6])],[(1,[z7,z2,z3,z379,z4,z5]),(0,[z538,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z539])],[(0,[z195,z2,z53,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z540,z6]),(0,[z7,z541,z2,z3,z4,z5,z6]),(0,[z542,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z543,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z544]),(0,[z7,z545,z2,z3,z4,z5,z6]),(0,[z7,z3,z4,z226,z5,z19,z6]),(0,[z7,z546,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z547]),(0,[z7,z2,z3,z4,z5,z277,z6])]],
   [[(0,[z7,z2,z3,z4,z5,z6,z548]),(0,[z7,z2,z294,z3,z4,z5,z6]),(0,[z7,z2,z3,z549,z4,z5,z6]),(0,[z7,z71,z2,z3,z85,z4,z6]),(0,[z7,z2,z124,z4,z15,z5,z6])],[(0,[z7,z2,z3,z4,z550,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z551]),(0,[z7,z2,z218,z164,z4,z5,z6])],[(0,[z552,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z193,z4,z178,z5,z6]),(0,[z7,z2,z553,z3,z4,z5,z6])],[(0,[z554,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z555]),(1,[z7,z2,z175,z4,z5,z6])],[(0,[z7,z2,z3,z4,z556,z5,z6]),(0,[z7,z557,z2,z3,z4,z5,z6]),(0,[z0,z323,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z558,z5,z6]),(0,[z7,z18,z2,z3,z4,z200,z6]),(1,[z7,z2,z3,z78,z5,z6]),(0,[z7,z559,z2,z3,z4,z5,z6]),(0,[z326,z2,z3,z4,z5,z155,z6]),(0,[z7,z560,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z561,z6]),(0,[z7,z562,z2,z3,z4,z5,z6]),(1,[z7,z2,z106,z4,z5,z6]),(0,[z7,z2,z563,z3,z4,z5,z6]),(0,[z7,z373,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z564,z4,z5,z6])],[(0,[z7,z2,z3,z13,z5,z6,z166]),(0,[z565,z7,z2,z3,z4,z5,z6]),(0,[z566,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z124,z4,z5,z6,z187])],[(0,[z7,z2,z567,z3,z4,z5,z6]),(0,[z7,z2,z3,z568,z4,z5,z6]),(0,[z195,z2,z3,z4,z5,z56,z6]),(0,[z7,z569,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z302])]],
   [[(0,[z570,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z3,z4,z200,z38])],[(0,[z7,z2,z571,z3,z4,z5,z6]),(0,[z7,z572,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z573])],[(0,[z7,z2,z3,z4,z5,z6,z574]),(0,[z7,z2,z3,z4,z5,z575,z6])],[(0,[z7,z2,z3,z4,z5,z576,z6]),(0,[z7,z2,z218,z162,z4,z5,z6]),(0,[z7,z2,z577,z3,z4,z5,z6]),(0,[z7,z18,z2,z3,z86,z4,z6]),(0,[z7,z33,z2,z12,z3,z4,z5]),(0,[z578,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z579,z5,z6])],[(0,[z7,z2,z3,z580,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z581,z6]),(0,[z195,z7,z2,z3,z11,z5,z6]),(0,[z7,z2,z582,z3,z4,z5,z6]),(0,[z7,z2,z3,z583,z4,z5,z6])],[(0,[z49,z7,z2,z3,z178,z5,z6]),(0,[z7,z2,z3,z4,z5,z34,z6])],[(0,[z7,z584,z2,z3,z4,z5,z6]),(0,[z228,z7,z2,z164,z4,z5,z6]),(1,[z10,z2,z3,z11,z5,z6]),(0,[z7,z2,z335,z3,z4,z178,z5]),(0,[z7,z37,z18,z2,z3,z4,z6])],[(0,[z0,z7,z2,z3,z4,z5,z54])]],
   [[(0,[z52,z1,z2,z3,z4,z5,z6]),(0,[z7,z2,z585,z3,z4,z5,z6]),(0,[z7,z2,z3,z379,z4,z5,z6]),(0,[z65,z7,z2,z3,z4,z5,z6])],[(0,[z586,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z587,z6]),(0,[z7,z2,z3,z4,z226,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z588])],[(0,[z47,z7,z2,z3,z4,z5,z6]),(0,[z7,z589,z2,z3,z4,z5,z6]),(0,[z49,z7,z2,z3,z31,z5,z6]),(0,[z7,z2,z3,z4,z590,z5,z6])],[(0,[z591,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z592,z4,z5,z6])],[(0,[z2,z3,z162,z4,z5,z107,z6]),(0,[z593,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z114,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z34,z166]),(0,[z7,z2,z3,z4,z594,z5,z6])],[(0,[z595,z7,z2,z3,z4,z5,z6]),(0,[z596,z7,z2,z3,z4,z5,z6]),(0,[z7,z230,z2,z3,z251,z5,z6]),(0,[z2,z3,z4,z5,z6,z368,z79])],[(0,[z7,z2,z3,z162,z4,z5,z6]),(0,[z7,z2,z3,z597,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z598])],[(0,[z599,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z600,z5,z6]),(0,[z7,z2,z3,z601,z4,z5,z6]),(0,[z7,z2,z3,z4,z602,z5,z6]),(0,[z7,z2,z3,z4,z5,z23,z6]),(0,[z151,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z133,z5,z6])]],
   [[(0,[z228,z7,z2,z162,z4,z5,z6]),(0,[z7,z2,z106,z3,z4,z5,z6]),(0,[z7,z2,z84,z3,z4,z19,z6]),(0,[z7,z2,z3,z4,z200,z5,z6])],[(0,[z7,z2,z3,z603,z4,z5,z6]),(0,[z48,z7,z2,z164,z4,z5,z6]),(0,[z7,z2,z3,z4,z604,z5,z6]),(0,[z7,z605,z2,z3,z4,z5,z6]),(1,[z7,z71,z3,z4,z19,z6]),(0,[z7,z2,z4,z5,z23,z6,z187]),(0,[z7,z606,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z251,z4,z31,z5])],[(0,[z7,z2,z607,z3,z4,z5,z6]),(0,[z7,z2,z608,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z609,z6]),(0,[z7,z610,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z611,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z43,z6])],[(0,[z612,z7,z2,z3,z4,z5,z6]),(0,[z7,z75,z2,z95,z4,z5,z6]),(0,[z613,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z614]),(0,[z7,z2,z41,z124,z4,z5,z6]),(0,[z7,z37,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z615,z5,z6])],[(0,[z7,z2,z616,z3,z4,z5,z6]),(0,[z7,z2,z3,z617,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z618]),(0,[z7,z2,z3,z251,z4,z5,z6]),(0,[z7,z2,z619,z3,z4,z5,z6])],[(0,[z93,z2,z3,z135,z4,z5,z6]),(0,[z7,z620,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z621,z6]),(0,[z7,z2,z3,z4,z5,z6,z79]),(0,[z622,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z623]),(0,[z7,z2,z3,z4,z5,z6,z624]),(0,[z2,z164,z150,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z625,z5,z6]),(0,[z7,z2,z84,z3,z4,z200,z6])],[(0,[z626,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z85,z4,z5,z6]),(0,[z7,z2,z627,z3,z4,z5,z6])]],
   [[(0,[z628,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z365,z4,z5,z6])],[],[(0,[z323,z10,z2,z3,z4,z5,z6]),(0,[z629,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z630,z3,z4,z5,z6]),(0,[z7,z2,z3,z631,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z632,z6]),(0,[z7,z2,z3,z4,z633,z5,z6]),(0,[z7,z2,z634,z3,z4,z5,z6])],[(0,[z7,z2,z41,z3,z124,z5,z6]),(0,[z7,z2,z3,z86,z4,z5,z6]),(0,[z7,z2,z3,z251,z4,z5,z166])],[(1,[z7,z635,z2,z3,z4,z6]),(0,[z7,z636,z2,z3,z4,z5,z6]),(0,[z90,z7,z2,z3,z4,z5,z6]),(0,[z637,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z638,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z168])],[(0,[z7,z2,z639,z3,z4,z5,z6]),(0,[z7,z2,z640,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z641,z5,z6]),(0,[z7,z2,z335,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z642,z6]),(0,[z7,z2,z12,z3,z251,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z643])],[(0,[z7,z2,z3,z4,z644,z5,z6]),(0,[z645,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z646,z5,z6]),(0,[z647,z7,z2,z3,z4,z5,z6]),(0,[z648,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z193,z4,z5,z6]),(0,[z90,z7,z2,z3,z444,z5,z6])],[(0,[z7,z649,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z650,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z651,z5,z6]),(0,[z7,z2,z3,z251,z5,z6,z166])],[(0,[z2,z122,z3,z4,z109,z5,z6]),(0,[z7,z2,z3,z4,z652,z5,z6])],[(0,[z195,z7,z2,z3,z135,z5,z6]),(0,[z7,z2,z653,z3,z4,z5,z6])],[(0,[z7,z2,z58,z4,z5,z23,z6])],[(0,[z323,z7,z2,z3,z4,z5,z56]),(0,[z7,z2,z58,z124,z4,z5,z6]),(0,[z7,z2,z3,z654,z4,z5,z6])],[(0,[z55,z7,z2,z164,z3,z4,z6]),(0,[z7,z2,z3,z4,z5,z6,z655]),(0,[z7,z2,z3,z4,z5,z656,z6]),(0,[z7,z33,z2,z3,z4,z5,z34]),(0,[z7,z657,z2,z3,z4,z5,z6])],[(0,[z7,z2,z658,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z659]),(0,[z7,z2,z660,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z661,z6]),(0,[z7,z2,z3,z662,z4,z5,z6]),(0,[z2,z12,z161,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z663,z6]),(0,[z7,z2,z664,z3,z4,z5,z6]),(0,[z7,z2,z3,z665,z4,z5,z6]),(0,[z47,z2,z3,z4,z109,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z666])]],
   [[(0,[z52,z2,z3,z4,z11,z5,z6]),(0,[z7,z2,z3,z4,z667,z5,z6]),(0,[z7,z230,z2,z3,z13,z5,z6]),(0,[z7,z2,z3,z4,z668,z5,z6])],[(0,[z228,z55,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z19,z6,z38]),(1,[z7,z2,z160,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z669])],[(0,[z52,z2,z3,z4,z5,z6,z54]),(0,[z7,z2,z3,z4,z5,z6,z670]),(0,[z7,z2,z3,z4,z5,z671,z6])],[(0,[z7,z2,z3,z4,z5,z6,z672]),(0,[z48,z2,z122,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z673]),(0,[z7,z2,z3,z4,z404,z5,z6]),(0,[z674,z7,z2,z3,z4,z5,z6]),(1,[z7,z2,z164,z4,z155,z6]),(0,[z675,z7,z2,z3,z4,z5,z6])],[(0,[z7,z2,z69,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z676,z5,z6]),(0,[z677,z7,z2,z3,z4,z5,z6]),(0,[z323,z2,z3,z4,z5,z56,z6]),(0,[z7,z2,z3,z4,z5,z6,z678]),(0,[z7,z216,z2,z95,z4,z5,z6]),(1,[z2,z3,z4,z256,z5,z6]),(0,[z7,z2,z3,z4,z679,z5,z6]),(1,[z7,z2,z3,z444,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z680]),(0,[z7,z2,z3,z4,z5,z6,z681])],[(0,[z7,z2,z682,z3,z4,z5,z6]),(0,[z7,z683,z2,z3,z4,z5,z6]),(0,[z684,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z319,z6,z79]),(0,[z7,z2,z3,z685,z4,z5,z6])],[(0,[z7,z2,z41,z59,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z686]),(0,[z687,z7,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z71,z2,z3,z86,z4,z6])],[(0,[z7,z2,z688,z3,z4,z5,z6]),(0,[z7,z2,z689,z3,z4,z5,z6]),(0,[z690,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z691,z4,z5,z6]),(1,[z2,z3,z4,z273,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6,z692]),(0,[z7,z2,z3,z4,z5,z693,z6]),(0,[z7,z2,z3,z4,z178,z5,z6]),(0,[z7,z2,z3,z4,z226,z6,z38]),(1,[z90,z7,z3,z4,z5,z79])],[(0,[z47,z7,z2,z164,z3,z4,z6]),(0,[z7,z2,z3,z4,z109,z155,z6]),(0,[z7,z2,z3,z4,z5,z19,z6]),(0,[z7,z2,z3,z4,z5,z6,z694]),(0,[z7,z2,z695,z3,z4,z5,z6])],[(0,[z696,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z697,z3,z4,z5,z6]),(0,[z7,z635,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z6,z698])],[(0,[z7,z2,z3,z4,z5,z699,z6]),(0,[z7,z2,z3,z4,z5,z6,z700]),(0,[z7,z2,z3,z4,z5,z6,z701])],[(0,[z7,z2,z3,z4,z5,z702,z6]),(0,[z703,z7,z2,z3,z4,z5,z6]),(0,[z49,z7,z2,z3,z251,z5,z6]),(0,[z7,z635,z2,z3,z4,z178,z6]),(0,[z704,z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z705,z5,z6])],[(0,[z7,z71,z37,z2,z3,z4,z6]),(0,[z7,z2,z3,z706,z4,z5,z6]),(0,[z7,z2,z3,z4,z31,z5,z6])]]]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
def bkB : List (List (List (ℕ × List W))) :=
  [[[(0,[z7,z71,z3,z4,z19,z6])],[(0,[z7,z2,z3,z707,z4,z5]),(0,[z2,z3,z162,z4,z45,z6]),(0,[z7,z2,z68,z4,z6,z302]),(0,[z7,z2,z3,z4,z314,z38]),(0,[z7,z2,z3,z4,z708,z38])],[(0,[z7,z2,z709,z4,z5,z6]),(0,[z7,z2,z229,z4,z50,z6]),(0,[z7,z2,z3,z710,z5,z6]),(0,[z2,z150,z4,z5,z155,z6]),(0,[z2,z3,z4,z5,z6,z711]),(0,[z7,z712,z2,z4,z5,z6])],[(0,[z7,z2,z713,z4,z5,z6])],[(0,[z714,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z715,z5,z6]),(0,[z7,z2,z3,z4,z716,z6]),(0,[z717,z2,z3,z4,z5,z6]),(0,[z7,z2,z4,z718,z5,z6])],[(0,[z213,z2,z3,z11,z5,z6]),(0,[z2,z150,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z719]),(0,[z7,z2,z3,z4,z720,z6]),(0,[z7,z2,z152,z4,z5,z6])],[(0,[z2,z3,z4,z109,z45,z6]),(0,[z2,z608,z3,z11,z5,z6]),(0,[z2,z161,z62,z4,z5,z6])]],
   [[(0,[z228,z2,z4,z305,z5,z6]),(0,[z49,z7,z3,z178,z67,z6]),(0,[z90,z7,z358,z4,z5,z79]),(0,[z2,z721,z3,z4,z5,z6])],[(0,[z7,z722,z2,z4,z5,z6]),(0,[z2,z162,z4,z5,z45,z6]),(0,[z47,z2,z150,z3,z4,z6]),(0,[z7,z2,z3,z4,z723,z6]),(0,[z7,z2,z379,z194,z4,z5]),(0,[z7,z2,z724,z4,z5,z6])],[],[(0,[z2,z162,z4,z107,z155,z6]),(0,[z7,z635,z2,z3,z4,z6]),(0,[z7,z2,z3,z725,z4,z5])],[(0,[z7,z2,z3,z4,z5,z726]),(0,[z7,z2,z3,z4,z727,z6]),(0,[z2,z3,z4,z5,z6,z728]),(0,[z7,z2,z3,z4,z729,z6]),(0,[z2,z161,z3,z4,z81,z6])],[(0,[z7,z2,z3,z730,z5,z6]),(0,[z2,z3,z4,z731,z5,z6])],[(0,[z2,z3,z732,z4,z5,z6]),(0,[z7,z2,z64,z146,z5,z6]),(0,[z7,z2,z3,z178,z5,z159])],[(0,[z93,z53,z3,z4,z5,z6]),(0,[z7,z2,z733,z4,z5,z6]),(0,[z30,z2,z3,z4,z43,z6])]],
   [[(0,[z7,z2,z734,z4,z5,z6]),(0,[z49,z7,z3,z178,z5,z159]),(0,[z7,z2,z164,z4,z735,z6])],[(0,[z7,z2,z736,z4,z5,z6]),(0,[z2,z3,z4,z737,z5,z6]),(0,[z7,z2,z3,z4,z738,z6]),(0,[z373,z2,z3,z318,z5,z6]),(0,[z7,z2,z739,z3,z4,z6])],[(0,[z740,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z741])],[(0,[z7,z2,z3,z31,z5,z159]),(0,[z231,z2,z193,z4,z5,z6]),(0,[z7,z2,z3,z4,z742,z6])],[(0,[z7,z2,z3,z4,z5,z743]),(0,[z744,z2,z3,z4,z5,z6]),(0,[z30,z2,z4,z5,z277,z6])],[(0,[z745,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z6,z746]),(0,[z2,z3,z379,z4,z256,z5]),(0,[z7,z230,z2,z3,z379,z5]),(0,[z90,z7,z3,z4,z319,z79]),(0,[z747,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z748,z5,z6]),(0,[z7,z2,z3,z4,z5,z749]),(0,[z7,z2,z3,z4,z750,z6]),(0,[z7,z2,z194,z4,z5,z6]),(0,[z7,z2,z3,z251,z444,z5])]],
   [[(0,[z7,z2,z160,z4,z5,z6])],[(0,[z7,z2,z3,z4,z751,z6]),(0,[z7,z2,z3,z752,z5,z6])],[(1,[z2,z162,z4,z45,z6]),(0,[z7,z2,z3,z4,z753,z6]),(0,[z2,z754,z3,z4,z5,z6]),(0,[z755,z2,z3,z4,z5,z6]),(0,[z7,z2,z164,z4,z155,z6])],[(0,[z55,z7,z2,z106,z4,z6]),(0,[z435,z2,z4,z5,z6,z302])],[(0,[z7,z2,z3,z756,z5,z6]),(0,[z7,z2,z3,z4,z757,z6]),(0,[z2,z3,z4,z256,z5,z6]),(0,[z228,z2,z66,z162,z4,z6]),(0,[z10,z2,z3,z301,z5,z6]),(0,[z2,z3,z4,z5,z758,z6]),(0,[z49,z231,z3,z178,z5,z6]),(0,[z151,z2,z62,z4,z5,z6])],[(0,[z7,z2,z3,z4,z759,z6]),(0,[z2,z3,z68,z4,z6,z368])],[(0,[z2,z106,z162,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z760]),(0,[z761,z2,z3,z4,z5,z6])],[(0,[z7,z2,z218,z297,z4,z6]),(0,[z7,z2,z229,z4,z5,z6]),(0,[z762,z2,z3,z4,z5,z6])]],
   [[(0,[z231,z2,z3,z4,z5,z6]),(0,[z7,z763,z3,z4,z5,z6]),(0,[z7,z2,z66,z203,z4,z6]),(0,[z48,z2,z106,z4,z5,z6]),(0,[z2,z3,z4,z273,z5,z6]),(0,[z7,z3,z4,z5,z764,z6])],[(0,[z7,z2,z122,z4,z45,z6]),(0,[z48,z2,z4,z223,z5,z6]),(0,[z7,z2,z3,z765,z4,z5]),(0,[z7,z2,z3,z4,z766,z5]),(0,[z90,z7,z3,z4,z5,z79]),(0,[z151,z2,z3,z4,z81,z6])],[(0,[z7,z2,z767,z3,z5,z6]),(0,[z49,z7,z3,z517,z5,z6]),(0,[z7,z2,z3,z768,z5,z6]),(0,[z7,z2,z627,z3,z6,z168])],[(0,[z49,z7,z3,z178,z50,z6]),(0,[z246,z2,z3,z4,z123,z6]),(0,[z90,z7,z3,z444,z5,z79]),(0,[z769,z2,z3,z4,z5,z6])],[(0,[z7,z2,z770,z4,z5,z6]),(0,[z7,z2,z771,z4,z5,z6]),(0,[z7,z2,z3,z4,z6,z772]),(0,[z2,z3,z773,z4,z5,z6])],[(0,[z7,z2,z3,z774,z4,z5])],[(0,[z30,z2,z69,z3,z4,z6])],[(0,[z7,z2,z775,z3,z5,z6]),(0,[z7,z2,z776,z4,z5,z6]),(0,[z2,z66,z150,z3,z4,z6]),(0,[z7,z170,z3,z4,z19,z6]),(0,[z7,z2,z3,z318,z123,z6]),(0,[z7,z2,z3,z4,z777,z5])]],
   [[(0,[z7,z2,z3,z4,z20,z6]),(0,[z7,z2,z276,z4,z123,z6])],[(0,[z48,z7,z2,z66,z4,z6]),(0,[z47,z2,z66,z3,z4,z6]),(1,[z55,z2,z106,z4,z6]),(0,[z7,z2,z4,z5,z6,z778]),(0,[z7,z635,z2,z194,z4,z6]),(0,[z779,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z780,z4,z5]),(0,[z7,z2,z3,z444,z20,z6]),(0,[z781,z2,z3,z4,z5,z6])],[(0,[z35,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z782,z6]),(0,[z2,z335,z3,z4,z256,z5]),(0,[z7,z2,z3,z4,z783,z6])],[(0,[z7,z2,z3,z4,z5,z40]),(0,[z7,z2,z3,z4,z67,z159]),(0,[z7,z635,z2,z193,z4,z6]),(0,[z7,z2,z3,z4,z43,z6]),(0,[z7,z2,z69,z175,z4,z6])],[(0,[z2,z3,z4,z5,z784,z6]),(0,[z2,z3,z4,z785,z5,z6]),(0,[z231,z2,z3,z379,z4,z5]),(0,[z786,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z787,z5,z6])],[(0,[z7,z2,z3,z788,z5,z6]),(0,[z228,z2,z17,z162,z4,z6]),(0,[z49,z3,z256,z178,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z789,z6]),(0,[z7,z2,z3,z264,z5,z166]),(0,[z373,z2,z3,z4,z123,z6]),(0,[z7,z2,z3,z365,z31,z5]),(0,[z7,z2,z4,z710,z5,z6]),(0,[z65,z2,z164,z4,z155,z6]),(0,[z790,z2,z3,z4,z5,z6]),(0,[z791,z2,z3,z4,z5,z6])],[(0,[z7,z2,z792,z3,z4,z5]),(0,[z7,z2,z4,z793,z5,z6]),(0,[z7,z2,z4,z5,z277,z6])],[(0,[z794,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z795,z6]),(0,[z2,z106,z150,z4,z5,z6])],[(0,[z7,z2,z796,z4,z5,z6]),(0,[z7,z2,z3,z4,z797,z5])],[(0,[z7,z2,z3,z4,z798,z6]),(1,[z2,z203,z4,z107,z6]),(0,[z7,z2,z3,z4,z5,z799]),(0,[z7,z2,z3,z4,z800,z6]),(0,[z7,z2,z3,z4,z5,z801]),(0,[z49,z7,z114,z178,z5,z6]),(0,[z802,z2,z3,z4,z5,z6]),(0,[z7,z2,z803,z4,z5,z6])],[(0,[z7,z2,z3,z804,z5,z6]),(0,[z7,z2,z3,z4,z805,z6]),(0,[z7,z244,z59,z4,z5,z6]),(0,[z806,z2,z3,z4,z5,z6]),(0,[z7,z2,z807,z4,z5,z6]),(0,[z7,z2,z3,z4,z808,z6]),(0,[z7,z2,z3,z4,z708,z200])],[(0,[z326,z2,z122,z4,z5,z6]),(0,[z7,z2,z809,z4,z5,z6])]],
   [[(0,[z2,z3,z4,z810,z5,z6])],[(0,[z2,z3,z4,z811,z5,z6]),(0,[z7,z2,z812,z3,z4,z6]),(0,[z7,z2,z150,z4,z155,z6]),(0,[z7,z2,z813,z4,z5,z6])],[(0,[z7,z2,z3,z4,z814,z6])],[],[(0,[z7,z2,z58,z4,z5,z204]),(0,[z7,z2,z815,z4,z5,z6]),(0,[z2,z816,z3,z4,z5,z6])],[(0,[z817,z2,z3,z4,z5,z6]),(0,[z35,z2,z3,z4,z5,z40]),(0,[z7,z2,z3,z4,z5,z818]),(0,[z7,z2,z819,z4,z5,z6]),(0,[z326,z7,z2,z164,z4,z6])],[(0,[z7,z2,z820,z4,z5,z6]),(0,[z2,z3,z4,z5,z821,z6]),(0,[z7,z2,z3,z4,z822,z6])],[(0,[z7,z2,z3,z823,z5,z6]),(0,[z7,z2,z66,z3,z4,z6]),(0,[z2,z66,z3,z4,z107,z6]),(0,[z7,z2,z3,z251,z5,z159]),(0,[z824,z2,z3,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z825])]],
   [[(0,[z7,z2,z826,z4,z5,z6]),(0,[z49,z182,z3,z178,z5,z6])],[(0,[z7,z22,z2,z4,z5,z666]),(0,[z7,z75,z638,z4,z5,z6]),(0,[z7,z2,z3,z4,z827,z6]),(0,[z7,z635,z2,z335,z3,z4]),(0,[z828,z2,z3,z4,z5,z6]),(0,[z7,z2,z4,z5,z829,z6])],[(0,[z7,z2,z3,z4,z5,z830]),(0,[z48,z2,z122,z4,z5,z6]),(0,[z7,z2,z3,z4,z831,z6]),(0,[z7,z2,z3,z4,z200,z247])],[(0,[z7,z2,z3,z4,z5,z832]),(0,[z326,z2,z3,z4,z5,z6]),(0,[z47,z2,z203,z4,z5,z6]),(0,[z55,z2,z203,z4,z107,z6]),(0,[z7,z2,z833,z3,z4,z6]),(0,[z7,z2,z69,z3,z4,z6])],[(0,[z7,z2,z834,z4,z5,z6]),(0,[z7,z2,z218,z203,z4,z6]),(0,[z2,z4,z5,z6,z302,z368]),(0,[z7,z2,z3,z4,z133,z6])],[(0,[z7,z2,z835,z4,z5,z6]),(0,[z7,z2,z836,z3,z4,z6]),(0,[z7,z2,z3,z4,z837,z6])],[(0,[z7,z2,z3,z365,z5,z159]),(0,[z49,z7,z335,z3,z178,z5]),(0,[z838,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z50,z159]),(0,[z246,z2,z3,z318,z5,z6]),(0,[z7,z2,z3,z4,z5,z839])]],
   [[(0,[z7,z2,z335,z3,z4,z5]),(0,[z246,z2,z276,z4,z5,z6])],[(0,[z7,z2,z3,z444,z5,z34]),(0,[z2,z175,z4,z273,z5,z6])],[(0,[z7,z2,z12,z3,z379,z5])],[(0,[z93,z577,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z840,z6])],[(0,[z2,z161,z3,z4,z5,z6]),(0,[z7,z2,z841,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z842]),(0,[z7,z2,z276,z318,z5,z6]),(0,[z7,z2,z3,z5,z6,z843])],[(0,[z182,z2,z114,z4,z5,z6]),(0,[z7,z2,z844,z4,z5,z6])],[(0,[z7,z2,z193,z335,z4,z5])],[(0,[z55,z2,z4,z404,z107,z6]),(0,[z2,z194,z4,z256,z5,z6]),(0,[z845,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z846,z6]),(0,[z2,z3,z847,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z825])]],
   [[(0,[z7,z2,z3,z848,z4,z6])],[(0,[z7,z2,z164,z4,z45,z6]),(0,[z7,z2,z3,z849,z5,z6]),(0,[z7,z2,z114,z4,z67,z6]),(0,[z7,z2,z850,z4,z5,z6])],[(0,[z7,z2,z851,z4,z5,z6]),(0,[z852,z2,z3,z4,z5,z6]),(0,[z7,z2,z4,z319,z6,z302]),(0,[z7,z2,z62,z4,z81,z6])],[],[(0,[z7,z2,z853,z4,z5,z6]),(0,[z231,z635,z2,z3,z4,z6]),(0,[z7,z2,z3,z6,z843,z168])],[(0,[z2,z3,z4,z5,z6,z368]),(0,[z373,z2,z276,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z54]),(0,[z7,z2,z3,z854,z5,z6])],[(0,[z2,z3,z4,z192,z5,z54]),(0,[z7,z2,z4,z5,z855,z6]),(0,[z7,z2,z3,z856,z5,z6])]],
   [[(0,[z7,z2,z4,z5,z857,z6]),(0,[z435,z2,z3,z365,z5,z6]),(0,[z326,z2,z4,z108,z5,z6]),(0,[z7,z22,z2,z4,z5,z187]),(0,[z7,z37,z2,z3,z6,z843])],[(0,[z7,z2,z3,z4,z858,z6]),(0,[z7,z2,z203,z4,z5,z6]),(0,[z7,z2,z3,z4,z859,z6]),(0,[z7,z2,z114,z4,z5,z159]),(0,[z7,z2,z3,z4,z5,z860]),(0,[z861,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z862,z5]),(0,[z7,z75,z59,z4,z5,z6]),(0,[z7,z2,z3,z13,z5,z159]),(0,[z7,z2,z3,z4,z6,z843])],[(0,[z7,z2,z3,z4,z863,z6]),(0,[z635,z2,z3,z4,z256,z6])],[(0,[z55,z2,z3,z4,z785,z6]),(0,[z7,z2,z3,z379,z444,z5]),(0,[z7,z2,z4,z5,z6,z864]),(0,[z90,z373,z3,z4,z5,z79])],[(0,[z7,z2,z3,z4,z865,z6]),(0,[z7,z2,z160,z444,z5,z6]),(0,[z90,z435,z3,z4,z5,z79])],[(0,[z7,z2,z3,z866,z5,z6]),(0,[z867,z2,z3,z4,z5,z6]),(0,[z868,z2,z3,z4,z5,z6])],[(0,[z47,z2,z311,z3,z4,z6]),(0,[z90,z7,z2,z3,z365,z5]),(0,[z435,z358,z2,z4,z5,z6]),(0,[z7,z358,z2,z365,z5,z6]),(0,[z7,z2,z329,z15,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z869,z6])],[(0,[z48,z2,z3,z4,z45,z6]),(0,[z151,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z6,z870]),(0,[z7,z2,z871,z4,z5,z6]),(0,[z90,z7,z160,z4,z5,z79])],[(0,[z328,z53,z3,z4,z5,z6]),(0,[z55,z2,z294,z4,z107,z6]),(0,[z182,z2,z3,z4,z67,z6]),(0,[z872,z2,z3,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z522]),(0,[z7,z2,z3,z4,z873,z6]),(0,[z7,z2,z874,z4,z5,z6]),(0,[z7,z2,z875,z4,z5,z6]),(0,[z7,z2,z876,z3,z4,z6])],[(0,[z2,z877,z162,z4,z5,z6]),(0,[z90,z246,z3,z4,z5,z79]),(0,[z7,z2,z4,z5,z878,z6])],[(0,[z879,z2,z3,z4,z5,z6]),(0,[z7,z83,z2,z3,z251,z5])],[(0,[z7,z2,z3,z4,z5,z880]),(0,[z2,z106,z4,z109,z5,z6]),(0,[z7,z649,z3,z4,z19,z6]),(0,[z435,z2,z3,z68,z4,z6]),(0,[z7,z881,z2,z3,z4,z6])]],
   [[(0,[z7,z2,z882,z4,z5,z6]),(0,[z7,z2,z3,z4,z883,z6]),(0,[z7,z2,z884,z4,z5,z6]),(0,[z7,z2,z3,z4,z764,z6]),(0,[z7,z2,z58,z4,z5,z454]),(0,[z7,z2,z3,z4,z885,z6])],[(0,[z7,z2,z886,z3,z4,z6]),(0,[z7,z2,z160,z4,z20,z6])],[(0,[z887,z2,z3,z4,z5,z6]),(0,[z49,z35,z3,z178,z5,z6])],[(0,[z7,z2,z888,z4,z5,z6]),(0,[z10,z2,z3,z889,z5,z6]),(0,[z182,z2,z3,z4,z5,z159]),(0,[z435,z2,z3,z4,z319,z6]),(0,[z7,z2,z3,z365,z319,z6])],[(0,[z2,z203,z4,z5,z107,z6]),(0,[z7,z2,z114,z4,z50,z6]),(0,[z7,z2,z3,z890,z4,z5]),(0,[z7,z2,z4,z735,z155,z6]),(0,[z326,z2,z164,z3,z4,z6])],[(0,[z7,z2,z3,z4,z5,z891]),(0,[z7,z2,z3,z4,z123,z6])],[(0,[z7,z2,z892,z4,z5,z6]),(0,[z7,z2,z3,z4,z893,z6]),(0,[z894,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z895,z6]),(0,[z2,z3,z4,z319,z6,z368]),(0,[z7,z358,z2,z68,z4,z6])],[(0,[z675,z7,z3,z178,z5,z6])]],
   [[(0,[z7,z2,z4,z5,z6,z896]),(0,[z7,z2,z3,z897,z5,z6])],[],[(0,[z7,z2,z3,z4,z5,z898]),(0,[z90,z7,z3,z4,z20,z79]),(0,[z7,z358,z2,z4,z319,z6])],[(0,[z7,z2,z3,z4,z899,z6]),(0,[z35,z2,z229,z4,z5,z6]),(0,[z7,z2,z193,z4,z177,z6]),(0,[z7,z2,z152,z4,z133,z6])],[(0,[z7,z2,z3,z4,z900,z6]),(0,[z7,z2,z229,z4,z5,z40])],[(0,[z7,z2,z3,z4,z901,z6]),(0,[z7,z2,z3,z4,z5,z902]),(0,[z2,z3,z4,z903,z5,z6]),(0,[z904,z2,z3,z4,z5,z6]),(0,[z7,z2,z905,z4,z5,z6]),(0,[z2,z3,z4,z273,z43,z6])],[(0,[z7,z2,z3,z4,z906,z6]),(0,[z435,z2,z3,z4,z5,z6]),(0,[z7,z2,z907,z3,z4,z6]),(0,[z7,z2,z203,z4,z107,z6]),(0,[z55,z2,z106,z4,z5,z6]),(0,[z908,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z365,z5,z6]),(0,[z49,z7,z193,z178,z5,z6]),(0,[z2,z3,z4,z5,z6,z909]),(0,[z7,z2,z3,z4,z910,z6]),(0,[z7,z2,z3,z251,z5,z166]),(0,[z2,z161,z3,z4,z133,z6])],[(0,[z7,z2,z3,z911,z5,z6]),(0,[z7,z2,z3,z4,z50,z6]),(0,[z7,z2,z3,z912,z5,z6]),(0,[z7,z2,z913,z4,z5,z6]),(0,[z7,z37,z2,z3,z6,z168])]],
   [[(0,[z7,z2,z351,z15,z5,z6])],[(0,[z7,z2,z294,z4,z5,z6]),(0,[z7,z2,z3,z914,z5,z6])],[(0,[z7,z2,z915,z4,z5,z6]),(0,[z7,z2,z916,z4,z5,z6]),(0,[z2,z3,z4,z109,z70,z6])],[(0,[z2,z3,z4,z5,z185,z6]),(0,[z47,z7,z2,z106,z4,z6]),(0,[z917,z2,z3,z4,z5,z6]),(0,[z7,z2,z918,z4,z5,z6]),(0,[z49,z7,z635,z3,z178,z6]),(0,[z919,z2,z3,z4,z5,z6]),(0,[z2,z161,z152,z4,z5,z6])],[(0,[z228,z2,z877,z4,z5,z6]),(0,[z7,z2,z920,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z302])],[(0,[z7,z2,z4,z921,z5,z6]),(0,[z7,z2,z3,z4,z5,z922]),(0,[z7,z2,z923,z4,z5,z6]),(0,[z7,z2,z3,z924,z5,z6]),(0,[z7,z358,z2,z4,z5,z6]),(0,[z90,z7,z4,z5,z302,z79]),(0,[z7,z2,z3,z365,z5,z166]),(0,[z7,z2,z925,z4,z5,z6])],[(0,[z182,z2,z3,z4,z50,z6]),(0,[z7,z2,z335,z3,z4,z177])],[(0,[z7,z2,z926,z4,z5,z6]),(0,[z7,z2,z877,z4,z5,z6]),(0,[z228,z2,z66,z3,z4,z6])]],
   [[(0,[z7,z2,z927,z3,z4,z6]),(0,[z48,z2,z4,z108,z107,z6]),(0,[z7,z2,z3,z4,z177,z6])],[],[(0,[z55,z2,z607,z3,z4,z6]),(0,[z7,z2,z3,z5,z928,z6])],[(0,[z7,z2,z3,z4,z929,z6]),(0,[z49,z7,z3,z178,z5,z6])],[(0,[z2,z930,z3,z4,z5,z6]),(0,[z7,z2,z931,z4,z5,z6]),(0,[z7,z2,z3,z932,z5,z6]),(0,[z933,z2,z3,z4,z5,z6]),(0,[z7,z2,z934,z4,z5,z6]),(0,[z935,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z936]),(0,[z7,z2,z3,z5,z937,z6]),(0,[z7,z3,z938,z178,z5,z6]),(0,[z49,z7,z2,z3,z379,z5]),(0,[z7,z2,z3,z4,z207,z38]),(0,[z7,z2,z3,z68,z4,z6]),(0,[z2,z3,z78,z5,z6,z368])],[(0,[z7,z2,z3,z4,z939,z6]),(0,[z326,z2,z164,z4,z155,z6])],[(0,[z7,z2,z940,z4,z5,z6]),(0,[z2,z3,z4,z5,z728,z54])]],
   [[(0,[z228,z2,z162,z4,z5,z6])],[(0,[z7,z2,z3,z4,z941,z6]),(0,[z7,z2,z942,z4,z5,z6]),(0,[z7,z2,z943,z4,z5,z6]),(0,[z7,z2,z114,z4,z5,z6]),(0,[z7,z2,z3,z4,z944,z6])],[(0,[z435,z2,z3,z78,z5,z6]),(0,[z945,z2,z3,z4,z5,z6])],[(0,[z151,z2,z3,z4,z133,z6])],[(0,[z7,z2,z3,z4,z946,z6]),(0,[z7,z2,z3,z4,z200,z430])],[(0,[z246,z2,z3,z4,z5,z6]),(0,[z7,z2,z947,z4,z5,z6]),(0,[z2,z3,z4,z785,z107,z6])],[(0,[z7,z2,z4,z948,z5,z6]),(0,[z7,z2,z3,z949,z5,z6])],[(0,[z7,z950,z2,z3,z4,z6]),(0,[z246,z2,z3,z444,z5,z6]),(0,[z2,z164,z150,z4,z155,z6]),(0,[z7,z2,z3,z4,z708,z5])]],
   [[(0,[z7,z2,z951,z3,z4,z5]),(0,[z7,z75,z394,z4,z5,z6]),(0,[z7,z2,z3,z4,z952,z6]),(0,[z675,z7,z3,z4,z5,z79]),(0,[z7,z2,z4,z735,z5,z6]),(0,[z953,z2,z3,z4,z5,z6]),(0,[z151,z2,z152,z4,z5,z6])],[(0,[z7,z2,z3,z318,z5,z6]),(0,[z231,z2,z335,z3,z4,z5]),(0,[z90,z7,z3,z4,z5,z954]),(0,[z7,z358,z2,z78,z5,z6])],[(0,[z7,z2,z276,z4,z5,z6]),(0,[z7,z2,z62,z4,z5,z6]),(0,[z955,z2,z3,z4,z5,z6])],[(0,[z55,z2,z106,z4,z107,z6]),(0,[z7,z2,z3,z4,z956,z6]),(0,[z7,z2,z3,z68,z78,z6])],[(0,[z7,z2,z710,z15,z5,z6])],[(0,[z7,z2,z3,z4,z957,z6]),(0,[z2,z66,z122,z3,z4,z6]),(0,[z7,z2,z17,z3,z4,z6]),(0,[z49,z7,z3,z178,z5,z40]),(0,[z7,z2,z3,z4,z958,z6])],[(0,[z93,z763,z3,z4,z5,z6]),(0,[z228,z2,z162,z4,z8,z6]),(0,[z7,z2,z3,z4,z959,z6]),(0,[z960,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z961,z5,z6]),(0,[z7,z2,z3,z4,z962,z6])],[(0,[z7,z2,z3,z4,z81,z6])]],
   [[(0,[z7,z2,z3,z5,z6,z963])],[(0,[z7,z2,z964,z4,z5,z6]),(0,[z326,z2,z3,z4,z45,z6]),(0,[z228,z2,z203,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z965]),(0,[z7,z2,z966,z4,z5,z6])],[(0,[z373,z2,z3,z4,z5,z6]),(0,[z2,z3,z4,z5,z6,z967]),(0,[z968,z2,z3,z4,z5,z6]),(0,[z7,z3,z4,z5,z6,z954])],[(0,[z182,z2,z3,z4,z5,z6])],[(0,[z7,z2,z66,z4,z155,z6]),(0,[z7,z2,z969,z4,z5,z6]),(0,[z373,z2,z3,z444,z5,z6])],[(0,[z228,z2,z150,z4,z5,z6]),(0,[z7,z2,z970,z3,z4,z6]),(0,[z7,z2,z12,z3,z444,z5])],[(0,[z7,z2,z162,z4,z45,z6]),(0,[z211,z2,z162,z4,z5,z6]),(0,[z7,z265,z2,z3,z6,z168]),(0,[z7,z2,z3,z4,z971,z6]),(0,[z2,z69,z3,z4,z273,z6])],[(0,[z2,z3,z877,z4,z5,z6]),(0,[z7,z2,z106,z4,z108,z6]),(0,[z7,z2,z3,z4,z67,z6]),(0,[z49,z7,z3,z379,z178,z5])]],
   [[(0,[z2,z972,z3,z4,z5,z6]),(0,[z7,z2,z218,z66,z4,z6]),(0,[z48,z2,z640,z4,z5,z6]),(0,[z7,z2,z973,z4,z5,z6])],[(0,[z7,z2,z974,z4,z5,z6]),(0,[z7,z2,z3,z975,z5,z6])],[(0,[z2,z3,z889,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z976]),(0,[z2,z977,z3,z4,z5,z6])],[(0,[z7,z2,z3,z978,z5,z6]),(0,[z7,z2,z3,z4,z979,z5]),(0,[z326,z2,z3,z4,z107,z6]),(0,[z231,z2,z194,z4,z5,z6]),(0,[z7,z2,z3,z365,z68,z6]),(0,[z7,z2,z3,z4,z980,z6])],[(0,[z981,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z444,z5,z79]),(0,[z7,z2,z982,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z983]),(0,[z7,z2,z3,z4,z5,z984])],[(0,[z7,z2,z3,z985,z5,z6]),(0,[z7,z2,z3,z4,z986,z6]),(0,[z7,z2,z3,z4,z987,z6]),(1,[z326,z2,z164,z4,z6])],[(0,[z7,z2,z3,z4,z988,z5]),(0,[z7,z2,z3,z4,z5,z159]),(0,[z2,z164,z4,z185,z155,z6]),(0,[z7,z2,z989,z4,z5,z6])]],
   [[(0,[z2,z763,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z990,z6]),(0,[z7,z2,z4,z404,z5,z6]),(0,[z7,z2,z3,z78,z5,z6]),(0,[z991,z2,z3,z4,z5,z6]),(0,[z2,z992,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z708,z6])],[(0,[z763,z53,z3,z4,z5,z6]),(0,[z55,z2,z150,z3,z4,z6]),(0,[z7,z2,z335,z194,z4,z5]),(0,[z7,z2,z3,z4,z735,z6])],[(0,[z7,z2,z3,z4,z5,z993]),(0,[z326,z2,z164,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z994]),(0,[z995,z2,z3,z4,z5,z6]),(0,[z7,z2,z996,z3,z4,z5]),(0,[z7,z2,z64,z710,z5,z6]),(0,[z7,z2,z3,z777,z5,z6])],[(0,[z7,z2,z3,z997,z5,z6]),(0,[z7,z2,z78,z5,z6,z302]),(0,[z7,z2,z3,z4,z200,z38])],[(0,[z998,z2,z3,z4,z5,z6])],[(0,[z7,z2,z160,z4,z123,z6])],[(0,[z7,z2,z999,z4,z5,z6]),(0,[z1000,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z4,z1001,z6]),(0,[z7,z2,z3,z4,z1002,z6]),(0,[z7,z2,z1003,z3,z5,z6]),(0,[z35,z2,z3,z4,z67,z6])],[(0,[z7,z2,z3,z1004,z5,z6]),(0,[z7,z2,z3,z4,z67,z40])],[(0,[z10,z2,z3,z11,z5,z6]),(0,[z49,z7,z3,z177,z178,z6]),(0,[z7,z2,z3,z444,z123,z6]),(0,[z7,z2,z3,z777,z5,z166])],[(0,[z48,z2,z877,z4,z5,z6]),(0,[z7,z2,z3,z1005,z5,z6]),(0,[z1006,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1007]),(0,[z7,z2,z4,z43,z277,z6])],[(0,[z7,z2,z1008,z4,z5,z6]),(0,[z7,z2,z3,z4,z1009,z6]),(0,[z7,z2,z3,z4,z1010,z6]),(0,[z7,z2,z3,z5,z1011,z6])],[(0,[z7,z2,z3,z4,z1012,z6]),(0,[z1013,z2,z3,z4,z5,z6]),(0,[z2,z218,z150,z4,z5,z6])],[(0,[z7,z1014,z2,z3,z4,z5]),(0,[z2,z3,z4,z5,z6,z1015])],[(0,[z55,z2,z3,z4,z45,z6]),(0,[z7,z3,z4,z938,z5,z6]),(0,[z90,z7,z3,z4,z123,z79])]],
   [[(0,[z35,z2,z3,z4,z5,z159])],[(0,[z7,z2,z3,z4,z1016,z6]),(0,[z7,z2,z3,z4,z5,z728])],[(0,[z30,z2,z3,z4,z5,z6]),(0,[z7,z2,z1017,z4,z5,z6])],[(0,[z2,z3,z1018,z4,z5,z6]),(0,[z7,z2,z3,z379,z5,z166]),(0,[z2,z1019,z3,z4,z5,z6]),(0,[z7,z2,z4,z303,z5,z187])],[(0,[z7,z2,z682,z4,z155,z6]),(0,[z7,z2,z3,z1020,z5,z6])],[(0,[z228,z2,z66,z4,z5,z6]),(0,[z2,z122,z877,z4,z5,z6]),(0,[z7,z545,z2,z4,z5,z187]),(0,[z7,z2,z1021,z4,z5,z6]),(0,[z2,z4,z273,z5,z277,z6])],[],[(0,[z7,z519,z59,z4,z5,z6]),(0,[z7,z2,z1022,z4,z5,z6]),(0,[z7,z2,z3,z4,z5,z1023]),(0,[z7,z2,z3,z4,z5,z1024]),(0,[z7,z2,z3,z251,z777,z5])]],
   [[(0,[z7,z2,z194,z4,z177,z6]),(0,[z90,z7,z3,z365,z5,z79])],[(0,[z55,z2,z3,z4,z107,z6])],[(0,[z7,z75,z736,z4,z5,z6]),(0,[z7,z2,z1025,z4,z5,z6])],[(0,[z7,z2,z3,z4,z1026,z6]),(0,[z7,z2,z4,z1027,z5,z6]),(0,[z49,z7,z194,z178,z5,z6]),(0,[z2,z1028,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1029])],[(0,[z7,z2,z1030,z3,z5,z6]),(0,[z7,z2,z1031,z4,z5,z6]),(0,[z326,z2,z203,z4,z5,z6]),(0,[z1032,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z1033,z4,z6])],[(0,[z10,z2,z3,z533,z5,z6]),(0,[z1034,z2,z3,z4,z5,z6]),(0,[z7,z2,z152,z4,z81,z6])],[(0,[z7,z2,z4,z5,z6,z1035]),(0,[z228,z2,z4,z108,z109,z6]),(0,[z7,z2,z3,z4,z1036,z6])]],
   [[(0,[z7,z2,z1037,z4,z5,z6]),(0,[z7,z2,z106,z4,z155,z6]),(0,[z1038,z2,z3,z4,z5,z6])],[(0,[z231,z2,z3,z4,z177,z6]),(0,[z2,z3,z4,z177,z256,z6]),(0,[z7,z2,z365,z5,z6,z302])],[(0,[z7,z2,z193,z4,z5,z6])],[(0,[z35,z2,z3,z4,z50,z6]),(0,[z49,z7,z229,z178,z5,z6]),(0,[z7,z2,z1039,z4,z5,z6]),(0,[z7,z2,z3,z1040,z4,z6])],[(0,[z7,z2,z1041,z4,z5,z6]),(0,[z7,z2,z3,z4,z50,z40]),(0,[z2,z3,z4,z1042,z5,z6]),(0,[z7,z2,z3,z4,z319,z6]),(0,[z7,z37,z2,z3,z289,z6])],[(0,[z1043,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1044,z6]),(0,[z90,z3,z4,z5,z368,z79]),(0,[z30,z2,z175,z4,z5,z6])],[(0,[z246,z2,z160,z4,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1045]),(0,[z90,z7,z3,z68,z4,z79]),(0,[z7,z2,z3,z4,z5,z954]),(0,[z90,z7,z3,z517,z4,z5]),(0,[z326,z2,z218,z3,z4,z6])]],
   [[(0,[z7,z736,z3,z4,z5,z6]),(0,[z7,z2,z1046,z4,z5,z6]),(0,[z7,z1047,z2,z3,z4,z6])],[(0,[z7,z2,z1048,z4,z5,z6]),(0,[z7,z2,z3,z4,z1049,z6]),(0,[z1050,z2,z3,z4,z5,z6])],[(0,[z140,z53,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z785,z6]),(0,[z2,z3,z4,z5,z6,z1051]),(0,[z7,z2,z160,z318,z5,z6]),(0,[z7,z22,z2,z4,z5,z555])],[(0,[z7,z2,z3,z1052,z5,z6])],[(0,[z48,z2,z150,z4,z5,z6]),(0,[z7,z2,z1053,z3,z5,z6])],[(1,[z228,z2,z66,z4,z6]),(0,[z7,z2,z3,z1054,z5,z6]),(0,[z1055,z2,z3,z4,z5,z6])],[(0,[z570,z2,z3,z4,z5,z54]),(0,[z7,z2,z64,z482,z5,z6])],[(0,[z7,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z4,z1056,z6]),(0,[z595,z2,z3,z4,z107,z6]),(0,[z7,z2,z193,z379,z4,z5]),(0,[z7,z2,z3,z379,z4,z177]),(0,[z7,z3,z4,z764,z19,z6]),(0,[z7,z2,z276,z444,z5,z6])]],
   [[(0,[z1057,z2,z3,z4,z5,z6]),(0,[z7,z71,z3,z4,z764,z6])],[(0,[z7,z2,z3,z4,z5,z1058]),(0,[z374,z7,z2,z164,z4,z6]),(0,[z47,z48,z2,z164,z4,z6]),(0,[z7,z2,z3,z4,z1059,z6]),(0,[z2,z3,z203,z4,z107,z6]),(0,[z7,z2,z3,z4,z1060,z6]),(0,[z1061,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z444,z5,z6]),(0,[z7,z2,z3,z4,z1062,z6])],[(0,[z2,z122,z203,z4,z5,z6]),(0,[z7,z2,z1063,z3,z4,z6]),(0,[z7,z2,z3,z4,z5,z1064])],[(0,[z7,z2,z3,z1065,z4,z5]),(0,[z7,z2,z4,z5,z6,z1066]),(0,[z373,z2,z160,z4,z5,z6]),(0,[z90,z7,z3,z318,z5,z79]),(0,[z1067,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z1068,z6]),(0,[z90,z7,z276,z4,z5,z79]),(0,[z7,z22,z2,z4,z5,z825])],[(0,[z7,z2,z1069,z4,z5,z6]),(0,[z35,z2,z114,z4,z5,z6]),(0,[z7,z2,z3,z1070,z5,z6])],[(0,[z228,z2,z162,z4,z45,z6]),(0,[z326,z2,z3,z4,z109,z6]),(0,[z7,z2,z114,z4,z5,z40]),(0,[z246,z2,z3,z4,z20,z6])],[(0,[z2,z3,z4,z1071,z5,z6])]],
   [[(0,[z1072,z2,z3,z4,z5,z6])],[(0,[z2,z122,z4,z5,z661,z6]),(0,[z7,z2,z164,z203,z4,z6]),(0,[z2,z1073,z3,z4,z5,z6])],[(0,[z7,z2,z4,z5,z1074,z6]),(0,[z7,z2,z3,z318,z20,z6]),(0,[z358,z2,z4,z5,z6,z368]),(0,[z2,z150,z3,z4,z155,z6]),(0,[z1075,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z4,z1076,z6]),(0,[z7,z2,z3,z4,z1077,z6]),(0,[z0,z2,z3,z4,z5,z728]),(0,[z1078,z2,z3,z4,z5,z6]),(0,[z182,z2,z229,z4,z5,z6]),(0,[z7,z2,z276,z4,z20,z6]),(0,[z7,z2,z1079,z4,z5,z6])],[(0,[z2,z1080,z3,z4,z5,z6]),(0,[z2,z193,z4,z256,z5,z6]),(0,[z7,z2,z3,z379,z4,z5]),(0,[z7,z2,z1081,z4,z5,z6]),(0,[z1082,z2,z3,z4,z5,z6]),(0,[z7,z2,z3,z517,z5,z166])],[(0,[z7,z2,z3,z4,z8,z6]),(0,[z7,z736,z59,z4,z5,z6]),(0,[z7,z2,z1083,z4,z5,z6]),(0,[z1084,z2,z3,z4,z5,z6]),(0,[z2,z3,z365,z5,z6,z368])],[(0,[z7,z2,z3,z1085,z5,z6]),(0,[z7,z2,z3,z4,z1086,z6]),(0,[z7,z2,z3,z1087,z5,z6]),(0,[z7,z37,z2,z3,z120,z6]),(0,[z7,z71,z503,z3,z4,z6]),(0,[z7,z2,z4,z5,z6,z1088]),(0,[z7,z2,z3,z1089,z5,z6])],[(0,[z7,z2,z1090,z4,z5,z6]),(0,[z7,z2,z229,z4,z67,z6]),(0,[z7,z2,z3,z5,z1091,z6]),(0,[z7,z2,z1092,z4,z5,z6])]],
   [[(0,[z7,z2,z3,z889,z5,z6]),(0,[z7,z2,z4,z5,z825,z187])],[(0,[z474,z2,z122,z4,z5,z6]),(0,[z1093,z2,z3,z4,z5,z6]),(0,[z7,z33,z2,z3,z365,z5]),(0,[z7,z2,z3,z4,z1094,z6]),(0,[z7,z2,z1095,z4,z5,z6])],[(0,[z7,z2,z3,z4,z45,z6]),(0,[z228,z55,z2,z164,z4,z6]),(0,[z47,z2,z218,z162,z4,z6]),(0,[z7,z2,z3,z4,z1096,z6]),(0,[z7,z2,z175,z4,z5,z6])],[(0,[z0,z2,z3,z4,z5,z236]),(0,[z93,z171,z3,z4,z5,z6]),(0,[z55,z2,z218,z122,z4,z6]),(0,[z7,z1097,z2,z4,z5,z6]),(0,[z373,z2,z3,z4,z20,z6])],[(0,[z7,z2,z1098,z4,z5,z6]),(0,[z7,z2,z1099,z4,z5,z6]),(0,[z7,z2,z106,z4,z5,z6])],[(0,[z65,z2,z3,z4,z5,z6]),(0,[z7,z2,z1100,z3,z4,z6]),(0,[z7,z2,z64,z15,z5,z6])],[(0,[z2,z122,z4,z109,z155,z6]),(0,[z7,z2,z4,z5,z6,z1101]),(0,[z7,z2,z3,z4,z5,z1102]),(0,[z7,z2,z1103,z4,z5,z6]),(0,[z7,z2,z1104,z4,z5,z6])],[(0,[z2,z1105,z3,z4,z5,z6]),(0,[z7,z2,z229,z4,z5,z159])]],
   [[(0,[z182,z2,z3,z4,z5,z40]),(0,[z2,z3,z1106,z4,z5,z6]),(0,[z1107,z2,z3,z4,z5,z6])],[(0,[z7,z2,z3,z938,z5,z6]),(0,[z7,z2,z3,z1108,z5,z6])],[(0,[z7,z2,z3,z1109,z5,z6]),(0,[z228,z7,z2,z66,z4,z6]),(0,[z90,z7,z3,z78,z5,z79])],[(0,[z7,z2,z1110,z4,z5,z6]),(0,[z49,z7,z3,z938,z5,z6])],[(0,[z7,z2,z3,z4,z5,z1111]),(0,[z7,z2,z203,z4,z109,z6])],[(0,[z55,z2,z106,z3,z4,z6]),(0,[z7,z635,z2,z3,z379,z4]),(0,[z7,z71,z3,z4,z460,z6]),(0,[z7,z2,z1112,z4,z5,z6]),(0,[z7,z2,z1113,z3,z5,z6])],[(0,[z7,z2,z3,z1114,z4,z6]),(0,[z7,z2,z4,z108,z431,z6]),(0,[z7,z1115,z2,z4,z5,z6]),(0,[z7,z2,z3,z4,z1116,z6]),(0,[z7,z2,z3,z319,z78,z6])],[(0,[z7,z2,z1117,z4,z5,z6]),(0,[z326,z2,z162,z4,z5,z6]),(0,[z7,z2,z4,z5,z6,z1118]),(0,[z7,z2,z3,z1119,z5,z6]),(0,[z1120,z2,z3,z4,z5,z6]),(0,[z1121,z2,z3,z4,z5,z6])]],
   [[(0,[z7,z2,z1122,z4,z5,z6]),(1,[z2,z150,z4,z155,z6])],[(0,[z7,z2,z3,z4,z1123,z6]),(0,[z2,z3,z1124,z4,z5,z6]),(0,[z675,z7,z2,z3,z251,z5])],[(0,[z2,z3,z889,z11,z5,z6])],[(1,[z2,z877,z4,z5,z6]),(0,[z7,z3,z4,z5,z954,z79])],[(0,[z1125,z2,z3,z4,z5,z6]),(0,[z7,z2,z1126,z4,z5,z6]),(0,[z2,z150,z3,z4,z108,z6]),(0,[z7,z2,z175,z4,z43,z6])],[(0,[z7,z1127,z2,z3,z5,z6]),(0,[z7,z2,z3,z1128,z4,z5]),(0,[z2,z3,z4,z5,z6,z1129]),(0,[z7,z2,z3,z1130,z4,z6])],[(0,[z7,z2,z1131,z3,z4,z6]),(0,[z7,z2,z69,z4,z277,z6])],[(0,[z7,z2,z106,z4,z45,z6]),(0,[z7,z2,z4,z108,z45,z6]),(0,[z7,z2,z3,z4,z1132,z6]),(0,[z7,z2,z3,z1133,z5,z6]),(0,[z7,z2,z62,z4,z133,z6])]]]

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
theorem pb2 : chunkB SB 1 ((bkA.flatten.flatten.drop 920).take 148) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pbend : ((bkA.flatten.flatten.drop 1068)).isEmpty = true := by
  decide +kernel

theorem windowsB : windowsG (chunkB SB 1) bkA.flatten.flatten 0 [460, 460, 148] = true :=
  windowsG_cons pb0 (windowsG_cons pb1 (windowsG_cons pb2 (windowsG_nil pbend)))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc0 : chunkOK 5 ((bkB.flatten.drop 0).take 144).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pc1 : chunkOK 5 ((bkB.flatten.drop 144).take 112).flatten = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pcend : ((bkB.flatten.drop 256)).isEmpty = true := by
  decide +kernel

theorem windowsC : windowsF 5 bkB.flatten 0 [144, 112] = true :=
  windowsF_cons pc0 (windowsF_cons pc1 (windowsF_nil pcend))

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

end PEqualNP.Outside.L_meta_47000

theorem PEqualNP.Outside.L_meta_47000 :
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3941264040 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3941264040 * 2 ^ 32 + 3936921768) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_47000.solve